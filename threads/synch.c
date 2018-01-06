/* This file is derived from source code for the Nachos
   instructional operating system.  The Nachos copyright notice
   is reproduced in full below. */

/* Copyright (c) 1992-1996 The Regents of the University of California.
   All rights reserved.

   Permission to use, copy, modify, and distribute this software
   and its documentation for any purpose, without fee, and
   without written agreement is hereby granted, provided that the
   above copyright notice and the following two paragraphs appear
   in all copies of this software.

   IN NO EVENT SHALL THE UNIVERSITY OF CALIFORNIA BE LIABLE TO
   ANY PARTY FOR DIRECT, INDIRECT, SPECIAL, INCIDENTAL, OR
   CONSEQUENTIAL DAMAGES ARISING OUT OF THE USE OF THIS SOFTWARE
   AND ITS DOCUMENTATION, EVEN IF THE UNIVERSITY OF CALIFORNIA
   HAS BEEN ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

   THE UNIVERSITY OF CALIFORNIA SPECIFICALLY DISCLAIMS ANY
   WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
   WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
   PURPOSE.  THE SOFTWARE PROVIDED HEREUNDER IS ON AN "AS IS"
   BASIS, AND THE UNIVERSITY OF CALIFORNIA HAS NO OBLIGATION TO
   PROVIDE MAINTENANCE, SUPPORT, UPDATES, ENHANCEMENTS, OR
   MODIFICATIONS.
*/

#include "threads/synch.h"
#include <stdio.h>
#include <string.h>
#include "threads/interrupt.h"
#include "threads/thread.h"


/* Initializes semaphore SEMA to VALUE.  A semaphore is a
   nonnegative integer along with two atomic operators for
   manipulating it:

   - down or "P": wait for the value to become positive, then
     decrement it.

   - up or "V": increment the value (and wake up one waiting
     thread, if any). */
void
sema_init (struct semaphore *sema, unsigned value)
{
    ASSERT (sema != NULL);

    sema->value = value;
    list_init (&sema->waiters);
}

/* Down or "P" operation on a semaphore.  Waits for SEMA's value
   to become positive and then atomically decrements it.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but if it sleeps then the next scheduled
   thread will probably turn interrupts back on. */
void
sema_down (struct semaphore *sema) {
    enum intr_level old_level;

    ASSERT (sema != NULL);
    ASSERT (!intr_context ());

    old_level = intr_disable ();
    while (sema->value == 0) {
        // replacing list_push_back with list_insert_ordered to account for priority scheduling in the semaphore waiting queue
        list_insert_ordered (&sema->waiters, &thread_current ()->elem, compare_thread_priorities, NULL);

        thread_block();
    }

    sema->value--;
    intr_set_level (old_level);
}

/* Down or "P" operation on a semaphore, but only if the
   semaphore is not already 0.  Returns true if the semaphore is
   decremented, false otherwise.

   This function may be called from an interrupt handler. */
bool
sema_try_down (struct semaphore *sema)
{
    enum intr_level old_level;
    bool success;

    ASSERT (sema != NULL);

    old_level = intr_disable ();
    if (sema->value > 0)
    {
        sema->value--;
        success = true;
    }
    else
        success = false;
    intr_set_level (old_level);

    return success;
}

/* Up or "V" operation on a semaphore.  Increments SEMA's value
   and wakes up one thread of those waiting for SEMA, if any.

   This function may be called from an interrupt handler. */
void
sema_up (struct semaphore *sema) {
    enum intr_level old_level;

    ASSERT(sema != NULL);

    old_level = intr_disable();

    struct thread *highest_priority_thread = NULL;

    while (!list_empty (&sema->waiters)) {
        // unblock the thread of the highest priority
        highest_priority_thread = list_entry(list_pop_front(&sema->waiters), struct thread, elem);
        thread_unblock(highest_priority_thread);
    }

    sema->value++;

    if (highest_priority_thread != NULL && highest_priority_thread->priority > thread_current()->priority) {
        yield_current_thread(thread_current());
    }

    intr_set_level(old_level);
}

static void sema_test_helper (void *sema_);

/* Self-test for semaphores that makes control "ping-pong"
   between a pair of threads.  Insert calls to printf() to see
   what's going on. */
void
sema_self_test (void)
{
    struct semaphore sema[2];
    int i;

    printf ("Testing semaphores...");
    sema_init (&sema[0], 0);
    sema_init (&sema[1], 0);
    thread_create ("sema-test", PRI_DEFAULT, sema_test_helper, &sema);
    for (i = 0; i < 10; i++)
    {
        sema_up (&sema[0]);
        sema_down (&sema[1]);
    }
    printf ("done.\n");
}

/* Thread function used by sema_self_test(). */
static void
sema_test_helper (void *sema_)
{
    struct semaphore *sema = sema_;
    int i;

    for (i = 0; i < 10; i++)
    {
        sema_down (&sema[0]);
        sema_up (&sema[1]);
    }
}

/* Initializes LOCK.  A lock can be held by at most a single
   thread at any given time.  Our locks are not "recursive", that
   is, it is an error for the thread currently holding a lock to
   try to acquire that lock.

   A lock is a specialization of a semaphore with an initial
   value of 1.  The difference between a lock and such a
   semaphore is twofold.  First, a semaphore can have a value
   greater than 1, but a lock can only be owned by a single
   thread at a time.  Second, a semaphore does not have an owner,
   meaning that one thread can "down" the semaphore and then
   another one "up" it, but with a lock the same thread must both
   acquire and release it.  When these restrictions prove
   onerous, it's a good sign that a semaphore should be used,
   instead of a lock. */
void
lock_init (struct lock *lock)
{
    ASSERT (lock != NULL);

    lock->holder = NULL;
    sema_init (&lock->semaphore, 1);
    lock->priority_lock = -1;
}

/* Acquires LOCK, sleeping until it becomes available if
   necessary.  The lock must not already be held by the current
   thread.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
lock_acquire (struct lock *lock)
{
    ASSERT (lock != NULL);
    ASSERT (!intr_context ());
    ASSERT (!lock_held_by_current_thread (lock));

    // turn off interrupts so that we can work with the current thread
    enum intr_level interrupt_state = intr_disable();

    // save the current thread, lock holder, and lock so we can use/modify them safely
    struct thread *current_thread = thread_current();
    struct thread *lock_holder = lock->holder;
    struct lock *lock_next = lock;
    int num_locks = 0 ;

    if (lock_holder != NULL) {
        // If the lock holder isn't NULL, then it must be blocking the current thread
        current_thread->blocker = lock;
    }

    while (lock_holder != NULL && lock_holder->priority < current_thread->priority) {
        // donate the priority of the current thread to the lock holder
        thread_set_priority_with_donation(lock_holder, current_thread->priority, true);

        // set the priority of the lock to that of the thread that is about to acquire it
        if (lock_next->priority_lock < current_thread->priority) {
            lock_next->priority_lock = current_thread->priority;
        }

        // if the lock holder is blocked by another thread with a lock,
        // then the lock to acquire is that thread which is blocking, so make that thread the new lock holder
        if (lock_holder->blocker != NULL && num_locks < 8) { // num_locks can be less than 8 per Stanford instructions
            lock_next = lock_holder->blocker;
            lock_holder = lock_holder->blocker->holder;
            num_locks++;
        }
        else {
            // once we assign a new lock holder, the lock has been acquired so the loop ends
            break;
        }
    }

    // call wait(), as the lock is about to be acquired
    sema_down (&lock->semaphore);

    // finally, make the current thread the lock holder
    lock->holder = current_thread;

    // the current thread has acquired the lock, so there is nothing blocking it now
    current_thread->blocker = NULL;

    // add the recently acquired lock to the thread's locks_held list
    list_insert_ordered (&current_thread->locks_held, &lock->elem_lock, compare_lock_priorities, NULL);

    // turn interrupts back on
    intr_set_level(interrupt_state);
}

/* Tries to acquires LOCK and returns true if successful or false
   on failure.  The lock must not already be held by the current
   thread.

   This function will not sleep, so it may be called within an
   interrupt handler. */
bool
lock_try_acquire (struct lock *lock)
{
    bool success;

    ASSERT (lock != NULL);
    ASSERT (!lock_held_by_current_thread (lock));

    success = sema_try_down (&lock->semaphore);
    if (success)
        lock->holder = thread_current ();

    return success;
}

/* Releases LOCK, which must be owned by the current thread.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to release a lock within an interrupt
   handler. */
void
lock_release (struct lock *lock) {
    ASSERT (lock != NULL);
    ASSERT (lock_held_by_current_thread (lock));

    // disable interrupts so that we can work with the current thread
    enum intr_level interrupt_state = intr_enable();

    // save the current thread
    struct thread *current_thread = thread_current();

    // this lock is being released, so it no longer has a holder
    lock->holder = NULL;

    // call signal() to free the semaphore
    sema_up(&lock->semaphore);

    // remove lock from the locks_held list
    list_remove (&lock->elem_lock);

    // reset lock to default
    lock->priority_lock = -1;

    // make sure the current thread has acquired lock
    if (list_empty(&current_thread->locks_held)) {

        // disregard any donated priority used in implementation
        current_thread->donated = false;

        thread_set_priority(current_thread->initial_priority);
    } else {
        // handle the case of multiple donation

        struct lock *lock_first = list_entry (list_front (&current_thread->locks_held), struct lock, elem_lock);

        // we donate the priority if there exists threads in the locks list
        if (lock_first->priority_lock != -1) {
            thread_set_priority_with_donation(current_thread, lock_first->priority_lock, true);
        } else {
            thread_set_priority(current_thread->initial_priority);
        }
    }

    // turn interrupts back on
    intr_set_level(interrupt_state);
}

/* Returns true if the current thread holds LOCK, false
   otherwise.  (Note that testing whether some other thread holds
   a lock would be racy.) */
bool
lock_held_by_current_thread (const struct lock *lock)
{
    ASSERT (lock != NULL);

    return lock->holder == thread_current ();
}

/* One semaphore in a list. */
struct semaphore_elem
{
    struct list_elem elem;              /* List element. */
    struct semaphore semaphore;         /* This semaphore. */
    int priority_sema;                  /* Make the waiting queue compatible with priority scheduling */
};

/* Initializes condition variable COND.  A condition variable
   allows one piece of code to signal a condition and cooperating
   code to receive the signal and act upon it. */
void
cond_init (struct condition *cond)
{
    ASSERT (cond != NULL);

    list_init (&cond->waiters);
}

/* Atomically releases LOCK and waits for COND to be signaled by
   some other piece of code.  After COND is signaled, LOCK is
   reacquired before returning.  LOCK must be held before calling
   this function.

   The monitor implemented by this function is "Mesa" style, not
   "Hoare" style, that is, sending and receiving a signal are not
   an atomic operation.  Thus, typically the caller must recheck
   the condition after the wait completes and, if necessary, wait
   again.

   A given condition variable is associated with only a single
   lock, but one lock may be associated with any number of
   condition variables.  That is, there is a one-to-many mapping
   from locks to condition variables.

   This function may sleep, so it must not be called within an
   interrupt handler.  This function may be called with
   interrupts disabled, but interrupts will be turned back on if
   we need to sleep. */
void
cond_wait (struct condition *cond, struct lock *lock)
{
    struct semaphore_elem waiter;

    ASSERT (cond != NULL);
    ASSERT (lock != NULL);
    ASSERT (!intr_context ());
    ASSERT (lock_held_by_current_thread (lock));

    sema_init (&waiter.semaphore, 0);

    // we wish to order the waiting elements by priority, as we're implementing priority scheduling
    waiter.priority_sema = thread_current ()->priority;
    list_insert_ordered (&cond->waiters, &waiter.elem, compare_semaphore_priorities, NULL);

    lock_release (lock);
    sema_down (&waiter.semaphore);
    lock_acquire (lock);
}

/* If any threads are waiting on COND (protected by LOCK), then
   this function signals one of them to wake up from its wait.
   LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_signal (struct condition *cond, struct lock *lock UNUSED)
{
    ASSERT (cond != NULL);
    ASSERT (lock != NULL);
    ASSERT (!intr_context ());
    ASSERT (lock_held_by_current_thread (lock));

    if (!list_empty (&cond->waiters))
        sema_up (&list_entry (list_pop_front (&cond->waiters),
                              struct semaphore_elem, elem)->semaphore);
}

/* Wakes up all threads, if any, waiting on COND (protected by
   LOCK).  LOCK must be held before calling this function.

   An interrupt handler cannot acquire a lock, so it does not
   make sense to try to signal a condition variable within an
   interrupt handler. */
void
cond_broadcast (struct condition *cond, struct lock *lock)
{
    ASSERT (cond != NULL);
    ASSERT (lock != NULL);

    while (!list_empty (&cond->waiters))
        cond_signal (cond, lock);
}


// Custom functions for priority scheduling

// returns true if the priority of the lhs semaphore is greater than the priority of the rhs semaphore
bool compare_semaphore_priorities(const struct list_elem *lhs, const struct list_elem *rhs, void *args) {
    if (lhs != NULL && rhs != NULL) {
        struct semaphore_elem *lhs_semaphore = list_entry(lhs, struct semaphore_elem, elem);
        struct semaphore_elem *rhs_semaphore = list_entry(rhs, struct semaphore_elem, elem);

        if (lhs_semaphore->priority_sema > rhs_semaphore->priority_sema) {
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}

// returns true if the priority of the lhs lock is greater than the priority of the rhs lock
bool compare_lock_priorities(const struct list_elem *lhs, const struct list_elem *rhs, void *args) {
    if (lhs != NULL && rhs != NULL) {
        struct lock *lhs_lock = list_entry(lhs, struct lock, elem_lock);
        struct lock *rhs_lock = list_entry(rhs, struct lock, elem_lock);

        if (lhs_lock->priority_lock >= rhs_lock->priority_lock) {
            return true;
        } else {
            return false;
        }
    } else {
        return false;
    }
}