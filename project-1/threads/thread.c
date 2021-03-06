#include "threads/thread.h"
#include <debug.h>
#include <stddef.h>
#include <random.h>
#include <stdio.h>
#include <string.h>
#include "threads/flags.h"
#include "threads/interrupt.h"
#include "threads/intr-stubs.h"
#include "threads/palloc.h"
#include "threads/switch.h"
#include "threads/synch.h"
#include "threads/vaddr.h"
#include "devices/timer.h"

#ifdef USERPROG
#include "userprog/process.h"
#endif

/* Random value for struct thread's `magic' member.
   Used to detect stack overflow.  See the big comment at the top
   of thread.h for details. */
#define THREAD_MAGIC 0xcd6abf4b

// fixed-point conversion formula that ends up getting reused multiple times in this file
#define FP_INT_CONVERT(x) ((x) >= 0 ? ((x) + (1 << (14)) / 2)\
                                   / (1 << (14)) : ((x) - (1 << (14)) / 2)\
                                   / (1 << (14)))


/* List of processes in THREAD_READY state, that is, processes
   that are ready to run but not actually running. */
static struct list ready_list;

// list for threads that are blocked (sleeping)
static struct list sleeping_threads;

// load_avg for advanced priority, fixed-point number
static int load_avg;


// List of all processes.
// Processes are added to this list when they are first scheduled and removed when they exit.
static struct list all_list;

// Idle thread
static struct thread *idle_thread;

/* Initial thread, the thread running init.c:main(). */
static struct thread *initial_thread;

/* Lock used by allocate_tid(). */
static struct lock tid_lock;

/* Stack frame for kernel_thread(). */
struct kernel_thread_frame
{
    void *eip;                  /* Return address. */
    thread_func *function;      /* Function to call. */
    void *aux;                  /* Auxiliary data for function. */
};

/* Statistics. */
static long long idle_ticks;    /* # of timer ticks spent idle. */
static long long kernel_ticks;  /* # of timer ticks in kernel threads. */
static long long user_ticks;    /* # of timer ticks in user programs. */

/* Scheduling. */
#define TIME_SLICE 4            /* # of timer ticks to give each thread. */
static unsigned thread_ticks;   /* # of timer ticks since last yield. */

/* If false (default), use round-robin scheduler.
   If true, use multi-level feedback queue scheduler.
   Controlled by kernel command-line option "-o mlfqs". */
bool thread_mlfqs;

static void kernel_thread (thread_func *, void *aux);

static void idle (void *aux UNUSED);
static struct thread *running_thread (void);
static struct thread *next_thread_to_run (void);
static void init_thread (struct thread *, const char *name, int priority);
static bool is_thread (struct thread *) UNUSED;
static void *alloc_frame (struct thread *, size_t size);
static void schedule (void);

void thread_schedule_tail (struct thread *prev);
static tid_t allocate_tid (void);

/* Initializes the threading system by transforming the code
   that's currently running into a thread.  This can't work in
   general and it is possible in this case only because loader.S
   was careful to put the bottom of the stack at a page boundary.

   Also initializes the run queue and the tid lock.

   After calling this function, be sure to initialize the page
   allocator before trying to create any threads with
   thread_create().

   It is not safe to call thread_current() until this function
   finishes. */
void
thread_init (void)
{
    ASSERT (intr_get_level () == INTR_OFF);

    lock_init (&tid_lock);
    list_init (&ready_list);
    list_init (&all_list);

    // create our custom sleeping_threads list
    list_init(&sleeping_threads);

    /* Set up a thread structure for the running thread. */
    initial_thread = running_thread ();
    init_thread (initial_thread, "main", PRI_DEFAULT);
    initial_thread->status = THREAD_RUNNING;
    initial_thread->tid = allocate_tid ();

    load_avg = 0;
}

/* Starts preemptive thread scheduling by enabling interrupts.
   Also creates the idle thread. */
void
thread_start (void)
{
    /* Create the idle thread. */
    struct semaphore idle_started;
    sema_init (&idle_started, 0);
    thread_create ("idle", PRI_MIN, idle, &idle_started);

    /* Start preemptive thread scheduling. */
    intr_enable ();

    /* Wait for the idle thread to initialize idle_thread. */
    sema_down (&idle_started);
}

/* Called by the timer interrupt handler at each timer tick.
   Thus, this function runs in an external interrupt context. */
void
thread_tick (void)
{
    struct thread *t = thread_current ();

    /* Update statistics. */
    if (t == idle_thread)
        idle_ticks++;
#ifdef USERPROG
        else if (t->pagedir != NULL)
    user_ticks++;
#endif
    else
        kernel_ticks++;

    /* Enforce preemption. */
    if (++thread_ticks >= TIME_SLICE)
        intr_yield_on_return ();

    // check if there are any sleeping (blocked) threads that need to be woken up
    wakeup_threads_if_needed();
}

/* Prints thread statistics. */
void
thread_print_stats (void)
{
    printf ("Thread: %lld idle ticks, %lld kernel ticks, %lld user ticks\n",
            idle_ticks, kernel_ticks, user_ticks);
}

/* Creates a new kernel thread named NAME with the given initial
   PRIORITY, which executes FUNCTION passing AUX as the argument,
   and adds it to the ready queue.  Returns the thread identifier
   for the new thread, or TID_ERROR if creation fails.

   If thread_start() has been called, then the new thread may be
   scheduled before thread_create() returns.  It could even exit
   before thread_create() returns.  Contrariwise, the original
   thread may run for any amount of time before the new thread is
   scheduled.  Use a semaphore or some other form of
   synchronization if you need to ensure ordering.

   The code provided sets the new thread's `priority' member to
   PRIORITY, but no actual priority scheduling is implemented.
   Priority scheduling is the goal of Problem 1-3. */
tid_t
thread_create (const char *name, int priority,
               thread_func *function, void *aux)
{
    struct thread *t;
    struct kernel_thread_frame *kf;
    struct switch_entry_frame *ef;
    struct switch_threads_frame *sf;
    tid_t tid;
    enum intr_level old_level;

    ASSERT (function != NULL);

    //Allocates the thread
    t = palloc_get_page (PAL_ZERO);
    if (t == NULL)
        return TID_ERROR;

    // Initializes the thread
    init_thread (t, name, priority);
    tid = t->tid = allocate_tid ();

    /* Prepare thread for first run by initializing its stack.
       Do this atomically so intermediate values for the 'stack'
       member cannot be observed. */
    old_level = intr_disable ();

    /* Stack frame for kernel_thread(). */
    kf = alloc_frame (t, sizeof *kf);
    kf->eip = NULL;
    kf->function = function;
    kf->aux = aux;

    /* Stack frame for switch_entry(). */
    ef = alloc_frame (t, sizeof *ef);
    ef->eip = (void (*) (void)) kernel_thread;

    /* Stack frame for switch_threads(). */
    sf = alloc_frame (t, sizeof *sf);
    sf->eip = switch_entry;
    sf->ebp = 0;

    intr_set_level (old_level);

    //to run queue
    thread_unblock (t);

    // The BSD scheduler does not allow threads to control their own priorities
    if (thread_mlfqs) {
        calculate_recent_cpu(t, NULL);
        calculate_advanced_priority(t, NULL);
        calculate_recent_cpu_for_thread();
        calculate_advanced_priority_for_thread();
    }

    if (t->priority > thread_current()->priority) {
        yield_current_thread(thread_current());
    }

    return tid;
}

/* Puts the current thread to sleep.  It will not be scheduled
   again until awoken by thread_unblock().

   This function must be called with interrupts turned off.  It
   is usually a better idea to use one of the synchronization
   primitives in synch.h. */
void
thread_block (void)
{
    ASSERT (!intr_context ());
    ASSERT (intr_get_level () == INTR_OFF);

    thread_current ()->status = THREAD_BLOCKED;
    schedule ();
}

/* Transitions a blocked thread T to the ready-to-run state.
   This is an error if T is not blocked.  (Use thread_yield() to
   make the running thread ready.)

   This function does not preempt the running thread.  This can
   be important: if the caller had disabled interrupts itself,
   it may expect that it can atomically unblock a thread and
   update other data. */
void
thread_unblock (struct thread *t)
{
    enum intr_level old_level;

    ASSERT (is_thread (t));

    old_level = intr_disable ();
    ASSERT (t->status == THREAD_BLOCKED);
    list_insert_ordered(&ready_list, &t->elem, compare_thread_priorities, NULL);
    t->status = THREAD_READY;
    intr_set_level (old_level);
}

/* Returns the name of the running thread. */
const char *
thread_name (void)
{
    return thread_current ()->name;
}

/* Returns the running thread.
   This is running_thread() plus a couple of sanity checks.
   See the big comment at the top of thread.h for details. */
struct thread *
thread_current (void)
{
    struct thread *t = running_thread ();

    /* Make sure T is really a thread.
       If either of these assertions fire, then your thread may
       have overflowed its stack.  Each thread has less than 4 kB
       of stack, so a few big automatic arrays or moderate
       recursion can cause stack overflow. */
    ASSERT (is_thread (t));
    ASSERT (t->status == THREAD_RUNNING);

    return t;
}

/* Returns the running thread's tid. */
tid_t
thread_tid (void)
{
    return thread_current ()->tid;
}

/* Deschedules the current thread and destroys it.  Never
   returns to the caller. */
void
thread_exit (void)
{
    ASSERT (!intr_context ());

#ifdef USERPROG
    process_exit ();
#endif

    /* Remove thread from all threads list, set our status to dying,
       and schedule another process.  That process will destroy us
       when it calls thread_schedule_tail(). */
    intr_disable ();
    list_remove (&thread_current()->allelem);
    thread_current ()->status = THREAD_DYING;
    schedule ();
    NOT_REACHED ();
}

/* Yields the CPU.  The current thread is not put to sleep and
   may be scheduled again immediately at the scheduler's whim. */
void
thread_yield (void)
{
    struct thread *cur = thread_current ();
    enum intr_level old_level;

    ASSERT (!intr_context ());

    old_level = intr_disable ();
    if (cur != idle_thread) {
        list_insert_ordered(&ready_list, &cur->elem, compare_thread_priorities, NULL);
    }
    cur->status = THREAD_READY;
    schedule ();
    intr_set_level (old_level);
}

/* Invoke function 'func' on all threads, passing along 'aux'.
   This function must be called with interrupts off. */
void
thread_foreach (thread_action_func *func, void *aux)
{
    struct list_elem *e;

    ASSERT (intr_get_level () == INTR_OFF);

    for (e = list_begin (&all_list); e != list_end (&all_list);
         e = list_next (e))
    {
        struct thread *t = list_entry (e, struct thread, allelem);
        func (t, aux);
    }
}

/* Sets the current thread's priority to NEW_PRIORITY.
 * ++ "If the current thread no longer has the highest priority, yields"
 */
void
thread_set_priority (int new_priority)
{
    thread_set_priority_with_donation(thread_current(), new_priority, false);
}

/* returns the current thread's priority. */
int thread_get_priority (void) {
    return thread_current()->priority;
}

// update a thread's nice value
void thread_set_nice(int new_nice) {
    ASSERT (new_nice >= NICE_MIN && new_nice <= NICE_MAX);

    struct thread *cur = thread_current();
    cur->nice = new_nice;

    // calculate_recent_cpu_for_thread ();
    calculate_advanced_priority_for_thread();

    // after updating the nice value, the priority will have changed
    // so update the ready list to make sure it remains sorted based on priority
    if (cur != idle_thread) {
        if (cur->status == THREAD_READY) {
            enum intr_level interrupt_state = intr_disable();

            list_remove (&cur->elem);
            list_insert_ordered (&ready_list, &cur->elem, compare_thread_priorities, NULL);

            intr_set_level(interrupt_state);
        } else if (cur->status == THREAD_RUNNING && list_entry(list_begin (&ready_list), struct thread, elem)->priority > cur->priority) {
            yield_current_thread(cur);
        }
    }
}

/* Returns the current thread's nice value. */
int thread_get_nice (void) {
    return thread_current()->nice;
}

/* Idle thread.  Executes when no other thread is ready to run.

   The idle thread is initially put on the ready list by
   thread_start().  It will be scheduled once initially, at which
   point it initializes idle_thread, "up"s the semaphore passed
   to it to enable thread_start() to continue, and immediately
   blocks.  After that, the idle thread never appears in the
   ready list.  It is returned by next_thread_to_run() as a
   special case when the ready list is empty. */
static void
idle (void *idle_started_ UNUSED)
{
    struct semaphore *idle_started = idle_started_;
    idle_thread = thread_current ();
    sema_up (idle_started);

    for (;;)
    {
        /* Let someone else run. */
        intr_disable ();
        thread_block ();

        /* Re-enable interrupts and wait for the next one.

           The `sti' instruction disables interrupts until the
           completion of the next instruction, so these two
           instructions are executed atomically.  This atomicity is
           important; otherwise, an interrupt could be handled
           between re-enabling interrupts and waiting for the next
           one to occur, wasting as much as one clock tick worth of
           time.

           See [IA32-v2a] "HLT", [IA32-v2b] "STI", and [IA32-v3a]
           7.11.1 "HLT Instruction". */
        asm volatile ("sti; hlt" : : : "memory");
    }
}

/* Function used as the basis for a kernel thread. */
static void
kernel_thread (thread_func *function, void *aux)
{
    ASSERT (function != NULL);

    intr_enable ();       /* The scheduler runs with interrupts off. */
    function (aux);       /* Execute the thread function. */
    thread_exit ();       /* If function() returns, kill the thread. */
}

/* Returns the running thread. */
struct thread *
running_thread (void)
{
    uint32_t *esp;

    /* Copy the CPU's stack pointer into `esp', and then round that
       down to the start of a page.  Because `struct thread' is
       always at the beginning of a page and the stack pointer is
       somewhere in the middle, this locates the curent thread. */
    asm ("mov %%esp, %0" : "=g" (esp));
    return pg_round_down (esp);
}

/* Returns true if T appears to point to a valid thread. */
static bool
is_thread (struct thread *t)
{
    return t != NULL && t->magic == THREAD_MAGIC;
}

/* Does basic initialization of T as a blocked thread named
   NAME. */
static void init_thread (struct thread *t, const char *name, int priority)
{
    ASSERT (t != NULL);
    ASSERT (PRI_MIN <= priority && priority <= PRI_MAX);
    ASSERT (name != NULL);

    memset (t, 0, sizeof *t);
    t->status = THREAD_BLOCKED;
    strlcpy (t->name, name, sizeof t->name);
    t->stack = (uint8_t *) t + PGSIZE;
    t->priority = priority;

    // Implementation for donation should use if (!thread_mlfqs)
    // mlfqs does not account for donation

    t->initial_priority = priority;
    t->donated = false;
    list_init (&t->locks_held);
    t->lock_blocked_by = NULL;

    // if we're using BSD scheduler
    if (thread_mlfqs) {
        if (t == initial_thread) {
            // the initial thread has a default niceness of 0
            t->nice = 0;

            // the initial thread has received 0 CPU recently
            t->recent_cpu = 0;
        } else {
            // if the thread is not initial, it inherits these values from its parent
            t->nice = thread_get_nice();
            t->recent_cpu = thread_get_recent_cpu();
        }
    }

    t->magic = THREAD_MAGIC;
    list_push_back (&all_list, &t->allelem);
}

/* Allocates a SIZE-byte frame at the top of thread T's stack and
   returns a pointer to the frame's base. */
static void *
alloc_frame (struct thread *t, size_t size)
{
    /* Stack data is always allocated in word-size units. */
    ASSERT (is_thread (t));
    ASSERT (size % sizeof (uint32_t) == 0);

    t->stack -= size;
    return t->stack;
}

/* Chooses and returns the next thread to be scheduled.  Should
   return a thread from the run queue, unless the run queue is
   empty.  (If the running thread can continue running, then it
   will be in the run queue.)  If the run queue is empty, return
   idle_thread. */
static struct thread *
next_thread_to_run (void)
{
    if (list_empty (&ready_list))
        return idle_thread;
    else
        return list_entry (list_pop_front (&ready_list), struct thread, elem);
}

/* Completes a thread switch by activating the new thread's page
   tables, and, if the previous thread is dying, destroying it.

   At this function's invocation, we just switched from thread
   PREV, the new thread is already running, and interrupts are
   still disabled.  This function is normally invoked by
   thread_schedule() as its final action before returning, but
   the first time a thread is scheduled it is called by
   switch_entry() (see switch.S).

   It's not safe to call printf() until the thread switch is
   complete.  In practice that means that printf()s should be
   added at the end of the function.

   After this function and its caller returns, the thread switch
   is complete. */
void
thread_schedule_tail (struct thread *prev)
{
    struct thread *cur = running_thread ();

    ASSERT (intr_get_level () == INTR_OFF);

    /* Mark us as running. */
    cur->status = THREAD_RUNNING;

    /* Start new time slice. */
    thread_ticks = 0;

#ifdef USERPROG
    /* Activate the new address space. */
  process_activate ();
#endif

    /* If the thread we switched from is dying, destroy its struct
       thread.  This must happen late so that thread_exit() doesn't
       pull out the rug under itself.  (We don't free
       initial_thread because its memory was not obtained via
       palloc().) */
    if (prev != NULL && prev->status == THREAD_DYING && prev != initial_thread)
    {
        ASSERT (prev != cur);
        palloc_free_page (prev);
    }
}

/* Schedules a new process.  At entry, interrupts must be off and
   the running process's state must have been changed from
   running to some other state.  This function finds another
   thread to run and switches to it.

   It's not safe to call printf() until thread_schedule_tail()
   has completed. */
static void
schedule (void)
{
    struct thread *cur = running_thread ();
    struct thread *next = next_thread_to_run ();
    struct thread *prev = NULL;

    ASSERT (intr_get_level () == INTR_OFF);
    ASSERT (cur->status != THREAD_RUNNING);
    ASSERT (is_thread (next));

    if (cur != next)
        prev = switch_threads (cur, next);
    thread_schedule_tail (prev);
}

/* Returns a tid to use for a new thread. */
static tid_t
allocate_tid (void)
{
    static tid_t next_tid = 1;
    tid_t tid;

    lock_acquire (&tid_lock);
    tid = next_tid++;
    lock_release (&tid_lock);

    return tid;
}

/* Offset of `stack' member within `struct thread'.
   Used by switch.S, which can't figure it out on its own. */
uint32_t thread_stack_ofs = offsetof (struct thread, stack);

// Custom functions for alarm

// returns whether or not the lhs element has a sleep time less than that of the rhs element
bool compare_sleep_ticks(const struct list_elem *lhs, const struct list_elem *rhs, void* args) {
    if (lhs != NULL && rhs != NULL) {
        const struct thread *lhs_element = list_entry(lhs, struct thread, elem);
        const struct thread *rhs_element = list_entry(rhs, struct thread, elem);

        if (lhs_element->sleep_time < rhs_element->sleep_time) {
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

// a getter for sleeping_threads
struct list* get_sleeping_threads(void) {
    return &sleeping_threads;
}

// unblocks a thread if it has slept for the appropriate amount of time
void wakeup_threads_if_needed(void) {

    // this needs to be updated before the end of the loop, so bring it outside
    struct list_elem *next_e;

    // iterate through our sleeping_list
    for (struct list_elem *e = list_begin(&sleeping_threads); e != list_end(&sleeping_threads); e = next_e) {

        /*
         * timer_ticks() is our clock. It keeps track of how much time has elapsed relative to sleep_time
         *
         * If sleep_time > time_ticks(), then the number of ticks equal to sleep_time has not passed
         * If sleep_time <= time_ticks(), then the number of ticks that has passed is at least equal to sleep time,
         *  meaning that it's time to wake the thread up
         *
         */

        struct thread *current_thread_in_list = list_entry(e, struct thread, elem);

        if (current_thread_in_list->sleep_time > timer_ticks()) {
            break;
        } else {
            // sleep_time is less than or equal clock time

            // turn off interrupts so we can work with the thread
            enum intr_level interrupt_state = intr_disable();

            // use the current element to get the next element before removing it from the list
            next_e = list_next(e);

            // remove the thread from the sleeping_list
            list_remove(e);

            // wake the thread up by unblocking it (because it is currently blocked/sleeping)
            thread_unblock(current_thread_in_list);

            // turn interrupts back on
            intr_set_level(interrupt_state);
        }
    }
}

// Custom functions for priority scheduling

// implementation of thread_set_priority to include priority donation (inheritance)
void thread_set_priority_with_donation(struct thread *current_thread, int new_priority, bool donate) {
    // disable interrupts so we can work with the current thread
    enum intr_level interrupt_state = intr_disable();

    if (!donate) {
        if (current_thread->donated && new_priority <= current_thread->priority)
            current_thread->initial_priority = new_priority;
        else
            current_thread->priority = current_thread->initial_priority = new_priority;
    } else {
        current_thread->priority = new_priority;
        current_thread->donated = true;
    }

    if (current_thread->status == THREAD_READY) {
        // if the thread is ready, it is already in the ready_list

        // no function exists that sorts the linked-list upon inserting,
        // so we insert by first removing the thread, then adding it back in orderly

        list_remove (&current_thread->elem);
        list_insert_ordered (&ready_list, &current_thread->elem, compare_thread_priorities, NULL);
    }
    else if (current_thread->status == THREAD_RUNNING) {
        struct thread *first_in_list = list_entry (list_begin (&ready_list), struct thread, elem);

        if (first_in_list->priority > current_thread->priority) {
            // if these things are true, yield the current thread
            yield_current_thread(current_thread);
        }
    }

    // turn interrupts back on
    intr_set_level(interrupt_state);
}

// yield the current thread
void yield_current_thread(struct thread *current_thread) {
    // disable interrupts so that we can work with the current thread
    enum intr_level interrupt_state = intr_disable();

    ASSERT (is_thread(current_thread));
    ASSERT (!intr_context ());

    if (current_thread != idle_thread) {
        list_insert_ordered(&ready_list, &current_thread->elem, compare_thread_priorities, NULL);
    }

    current_thread->status = THREAD_READY;
    schedule ();

    // turn interrupts back on
    intr_set_level (interrupt_state);
}

// returns whether or not the lhs priority is greater than the rhs priority
bool compare_thread_priorities(const struct list_elem *lhs, const struct list_elem *rhs, void* args) {
    if (lhs != NULL && rhs != NULL) {
        const struct thread *lhs_element = list_entry(lhs, struct thread, elem);
        const struct thread *rhs_element = list_entry(rhs, struct thread, elem);

        if (lhs_element->priority > rhs_element->priority) {
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

// Custom functions for advanced scheduler

//returns the system load average * 100
int thread_get_load_avg (void) { return FP_INT_CONVERT(((load_avg) * (100))); }

//returns the recent_cpu value value * 100
int thread_get_recent_cpu (void) { return FP_INT_CONVERT(((thread_current()->recent_cpu) * (100))); }

// run the calculate_advanced_priority function for the current thread
void calculate_advanced_priority_for_thread(void) { calculate_advanced_priority(thread_current(), NULL); }

// runs the calculated_advanced_priority function for every thread in the system
void calculate_advanced_priority_for_all_threads(void) {
    thread_foreach (calculate_advanced_priority, NULL);

    // now that we have recalculated priorities, make sure the ready_list stays sorted
    if (!list_empty(&ready_list)) {
        list_sort(&ready_list, compare_thread_priorities, NULL);
    }
}

// determines thread priority for BSD scheduling with the formula priority = PRI_MAX - (recent_cpu / 4) - (nice * 2)
void calculate_advanced_priority (struct thread *cur, void *aux UNUSED) {
    if (cur != idle_thread) {
        // adjust the priority to be between PRI_MIN and PRI_MAX (0 - 63)
        cur->priority = PRI_MAX - FP_INT_CONVERT(((cur->recent_cpu) / (4))) - cur->nice * 2;

        // check if the priority is still in the priority boundary and handle accordingly
        if (cur->priority < PRI_MIN) {
            cur->priority = PRI_MIN;
        } else if (cur->priority > PRI_MAX) {
            cur->priority = PRI_MAX;
        }
    }
}

// runs the calculate_recent_cpu function for the current thread
void calculate_recent_cpu_for_thread(void) { calculate_recent_cpu(thread_current(), NULL); }

// runs the calculate_recent_cpu_for_all_threads function for every thread
void calculate_recent_cpu_for_all_threads(void) { thread_foreach (calculate_recent_cpu, NULL); }

// calculates the recent_cpu value with the formula
// recent_cpu = (2*load_avg)/(2*load_avg + 1) * recent_cpu + nice
void calculate_recent_cpu (struct thread *cur, void *aux UNUSED) {
    if (cur != idle_thread) {
        // do the calculation using fixed-point conversions
        int load = ((load_avg) * (2));
        int coefficient = ((int64_t)(load)) * (1 << (14)) / ((load) + 1 * (1 << (14)));
        cur->recent_cpu = (((int64_t)(coefficient)) * (cur->recent_cpu) / (1 << (14))) + (cur->nice) * (1 << (14));
    }
}

// calculates the load_avg with the formula
// load_avg = (59/60)*load_avg + (1/60)*ready_threads
void calculate_load_avg (void) {
    struct thread *cur = thread_current();
    int ready_list_threads = list_size(&ready_list);

    int num_ready_threads;
    // a thread that is idle is not a ready thread
    if (cur != idle_thread) {
        num_ready_threads = ready_list_threads + 1;
    } else {
        num_ready_threads = ready_list_threads;
    }

    // do the calculation using fixed-point conversions
    load_avg = ((int64_t)(((59 * (1 << (14))) / (60)))) * (load_avg) / (1 << (14)) + ((((1 * (1 << (14))) / (60))) * (num_ready_threads));
}