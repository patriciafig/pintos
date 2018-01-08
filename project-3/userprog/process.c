#include "userprog/process.h"
#include <debug.h>
#include <inttypes.h>
#include <round.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "userprog/gdt.h"
#include "userprog/pagedir.h"
#include "userprog/tss.h"
#include "filesys/directory.h"
#include "filesys/file.h"
#include "filesys/filesys.h"
#include "threads/flags.h"
#include "threads/init.h"
#include "threads/interrupt.h"
#include "threads/malloc.h"
#include "threads/palloc.h"
#include "threads/thread.h"
#include "threads/vaddr.h"
#include "devices/timer.h"
#include "userprog/syscall.h"
#include "vm/frame.h"

struct mmfile {
    mapid_t mapid;
    struct file* file;
    void * start_addr;
    unsigned pg_cnt;
    struct hash_elem elem;
};

static thread_func start_process NO_RETURN;
static bool load (const char *cmdline, void (**eip) (void), void **esp);

// Custom functions for Virtual Memory

unsigned mmfile_hash(const struct hash_elem *, void *);
bool mmfile_less(const struct hash_elem *, const struct hash_elem *, void *);
void free_mmfiles(struct hash *);
static void free_mmfiles_entry(struct hash_elem *, void *);
static void mmfiles_free_entry(struct mmfile* mmf_ptr);
static mapid_t alloc_mapid(void);

/* Starts a new thread running a user program loaded from
   FILENAME.  The new thread may be scheduled (and may even exit)
   before process_execute() returns.  Returns the new process's
   thread id, or TID_ERROR if the thread cannot be created. */
tid_t
process_execute (const char *file_name)
{
    char *fn_copy;
    tid_t tid;

    /* Make a copy of FILE_NAME.
         Otherwise there's a race between the caller and load(). */
    fn_copy = palloc_get_page (0);
    if (fn_copy == NULL)
        return TID_ERROR;

    // the file_name is copied into a new variable
    strlcpy (fn_copy, file_name, PGSIZE);

    char *args;

    // split the filename by spaces, taking only the characters before the first space
    char *command_name = strtok_r(fn_copy, " ", &args);

    // preallocate this so that we can use its size with calloc
    struct child_status *child;

    /* Create a new thread to execute FILE_NAME. */
    tid = thread_create(command_name, PRI_DEFAULT, start_process, args);
    if (tid == TID_ERROR) {
        // prevent a page fault
        palloc_free_page(fn_copy);
    } else {
        child = calloc(1, sizeof *child);

        if (child != NULL) {
            // put the process information into the child, then put the child on the thread's children list
            child->child_id = tid;
            child->is_exit_called = false;
            child->has_been_waited = false;
            list_push_back(&thread_current()->children, &child->elem_child_status);
        }
    }

    return tid;
}

/* A thread function that loads a user process and starts it
   running. */
static void
start_process (void *file_name_)
{
    char *file_name = file_name_;
    struct intr_frame if_;
    bool success;

    // create the suppl. hash table and the mmfiles table
    hash_init(&thread_current()->suppl_page_table, suppl_pt_hash, suppl_pt_less, NULL);
    hash_init(&thread_current()->mmfiles, mmfile_hash, mmfile_less, NULL);

    /* Initialize interrupt frame and load executable. */
    memset (&if_, 0, sizeof if_);
    if_.gs = if_.fs = if_.es = if_.ds = if_.ss = SEL_UDSEG;
    if_.cs = SEL_UCSEG;
    if_.eflags = FLAG_IF | FLAG_MBS;

    success = load (file_name, &if_.eip, &if_.esp);

    int load_status;
    if (!success) {
        load_status = -1;
    } else {
        load_status = 1;
    }

    struct thread *parent = thread_get_by_id(thread_current()->parent_id);

    if (parent != NULL) {
        // acquire a lock on the parent's child so that we can update its status
        lock_acquire(&parent->lock_child);

        // the assembly handles starting the process, we just update the success state here
        parent->child_load_status = load_status;

        // release the lock on the parent's child, as we no longer need to modify the child
        cond_signal(&parent->cond_child, &parent->lock_child);
        lock_release(&parent->lock_child);
    }

    /* If load failed, quit. */
    if (!success) {
        thread_exit();
    }

    // we no longer the page related to the file name in memory since the process execution has either begun or failed
    palloc_free_page(pg_round_down(file_name));

    /* Start the user process by simulating a return from an
        interrupt, implemented by intr_exit (in
        threads/intr-stubs.S).  Because intr_exit takes all of its
        arguments on the stack in the form of a `struct intr_frame',
        we just point the stack pointer (%esp) to our stack frame
        and jump to it. */
    asm volatile ("movl %0, %%esp; jmp intr_exit" : : "g" (&if_) : "memory");
    NOT_REACHED ();
}

/* Waits for thread TID to die and returns its exit status.  If
   it was terminated by the kernel (i.e. killed due to an
   exception), returns -1.  If TID is invalid or if it was not a
   child of the calling process, or if process_wait() has already
   been successfully called for the given TID, returns -1
   immediately, without waiting. */
int process_wait(tid_t child_tid) {
    // this function finds the child thread and sets its has_been_waited value if the situation calls for it
    int status;
    if (child_tid != TID_ERROR) {
        struct child_status *child = NULL;
        struct thread *current_thread = thread_current();
        struct list_elem *e = list_tail (&current_thread->children);

        // find the child thread in the current thread's children
        while ((e = list_prev (e)) != list_head(&current_thread->children)) {
            child = list_entry(e, struct child_status, elem_child_status);

            if (child->child_id == child_tid) {
                break;
            }
        }

        if (child == NULL) {
            status = -1;
        } else {
            // acquire a lock on the child thread so we can modify it
            lock_acquire(&current_thread->lock_child);

            while (thread_get_by_id(child_tid) != NULL) {
                cond_wait(&current_thread->cond_child, &current_thread->lock_child);
            }

            if (!child->is_exit_called || child->has_been_waited) {
                status = -1;
            } else {
                status = child->child_exit_status;

                // this is the only value for child we need to modify
                child->has_been_waited = true;
            }

            // release the lock on the child, as we no longer need to modify it
            lock_release(&current_thread->lock_child);
        }
    } else {
        status = TID_ERROR;
    }

    // status is -1 if child was not found, exit was called on it, or it has been waiting
    return status;
}

/* Free the current process's resources. */
void process_exit (void) {
    struct thread *current_thread = thread_current();

    // first, deallocate all memory mapped files
    free_mmfiles(&thread_current()->mmfiles);

    // by setting this value, we reset back to the kernel's page directory
    uint32_t *pd = current_thread->pagedir;

    if (pd != NULL) {
        // now that we've switched to the kernel page directory, we no longer need this value
        current_thread->pagedir = NULL;

        // activate the default page directory so that we don't remove the page directory we're using
        pagedir_activate(NULL);

        // we can now get rid of the process's page directory
        pagedir_destroy(pd);
    }

    struct list_elem *e = list_begin(&current_thread->children);
    struct child_status *current_child;
    struct list_elem *next_child;

    // go through all of the current thread's children and free them one by one
    while (e != list_tail(&current_thread->children)) {
        next_child = list_next(e);

        current_child= list_entry(e, struct child_status, elem_child_status);
        list_remove(e);
        free(current_child);

        e = next_child;
    }

    // now that the process has executed, it is allowed to be modified again
    if (current_thread->exec_file != NULL) {
        file_allow_write(current_thread->exec_file);
    }

    // any files opened up the the current thread can now be released
    close_file_by_owner(current_thread->tid);

    // deallocate the suppl. page table
    free_suppl_pt(&thread_current()->suppl_page_table);

    struct thread *parent = thread_get_by_id(current_thread->parent_id);

    if (parent != NULL) {
        // acquire a lock on the parent so we can update it
        lock_acquire(&parent->lock_child);

        if (parent->child_load_status == 0) {
            parent->child_load_status = -1;
        }

        // release the lock on the parent
        cond_signal(&parent->cond_child, &parent->lock_child);
        lock_release(&parent->lock_child);
     }
 }

/* Sets up the CPU for running user code in the current
   thread.
   This function is called on every context switch. */
void
process_activate (void)
{
  struct thread *t = thread_current ();

  /* Activate thread's page tables. */
  pagedir_activate (t->pagedir);

  /* Set thread's kernel stack for use in processing
     interrupts. */
  tss_update ();
}

/* We load ELF binaries.  The following definitions are taken
   from the ELF specification, [ELF1], more-or-less verbatim.  */

/* ELF types.  See [ELF1] 1-2. */
typedef uint32_t Elf32_Word, Elf32_Addr, Elf32_Off;
typedef uint16_t Elf32_Half;

/* For use with ELF types in printf(). */
#define PE32Wx PRIx32   /* Print Elf32_Word in hexadecimal. */
#define PE32Ax PRIx32   /* Print Elf32_Addr in hexadecimal. */
#define PE32Ox PRIx32   /* Print Elf32_Off in hexadecimal. */
#define PE32Hx PRIx16   /* Print Elf32_Half in hexadecimal. */

/* Executable header.  See [ELF1] 1-4 to 1-8.
   This appears at the very beginning of an ELF binary. */
struct Elf32_Ehdr
  {
    unsigned char e_ident[16];
    Elf32_Half    e_type;
    Elf32_Half    e_machine;
    Elf32_Word    e_version;
    Elf32_Addr    e_entry;
    Elf32_Off     e_phoff;
    Elf32_Off     e_shoff;
    Elf32_Word    e_flags;
    Elf32_Half    e_ehsize;
    Elf32_Half    e_phentsize;
    Elf32_Half    e_phnum;
    Elf32_Half    e_shentsize;
    Elf32_Half    e_shnum;
    Elf32_Half    e_shstrndx;
  };

/* Program header.  See [ELF1] 2-2 to 2-4.
   There are e_phnum of these, starting at file offset e_phoff
   (see [ELF1] 1-6). */
struct Elf32_Phdr
  {
    Elf32_Word p_type;
    Elf32_Off  p_offset;
    Elf32_Addr p_vaddr;
    Elf32_Addr p_paddr;
    Elf32_Word p_filesz;
    Elf32_Word p_memsz;
    Elf32_Word p_flags;
    Elf32_Word p_align;
  };

/* Values for p_type.  See [ELF1] 2-3. */
#define PT_NULL    0            /* Ignore. */
#define PT_LOAD    1            /* Loadable segment. */
#define PT_DYNAMIC 2            /* Dynamic linking info. */
#define PT_INTERP  3            /* Name of dynamic loader. */
#define PT_NOTE    4            /* Auxiliary info. */
#define PT_SHLIB   5            /* Reserved. */
#define PT_PHDR    6            /* Program header table. */
#define PT_STACK   0x6474e551   /* Stack segment. */

/* Flags for p_flags.  See [ELF3] 2-3 and 2-4. */
#define PF_X 1          /* Executable. */
#define PF_W 2          /* Writable. */
#define PF_R 4          /* Readable. */

static bool setup_stack (void **esp, const char *file_name);
static bool validate_segment (const struct Elf32_Phdr *, struct file *);
static bool load_segment (struct file *file, off_t ofs, uint8_t *upage,
                          uint32_t read_bytes, uint32_t zero_bytes,
                          bool writable);
static bool load_segment_lazily(struct file *file, off_t ofs, uint8_t *upage, uint32_t read_bytes, uint32_t zero_bytes, bool writable);

/* Loads an ELF executable from FILE_NAME into the current thread.
   Stores the executable's entry point into *EIP
   and its initial stack pointer into *ESP.
   Returns true if successful, false otherwise. */
bool
load (const char *file_name, void (**eip) (void), void **esp)
{
  struct thread *t = thread_current();
  struct Elf32_Ehdr ehdr;
  struct file *file = NULL;
  off_t file_ofs;
  bool success = false;
  int i;

  /* Allocate and activate page directory. */
  t->pagedir = pagedir_create ();
  if (t->pagedir == NULL)
    goto done;
  process_activate ();

  /* Open executable file. */
  // Removed this because the file is parsed out to be the the thread name, and the argument to file_name is arg_string
  file = filesys_open(t->name);
  if (file == NULL) {
      printf("load: %s: open failed\n", t->name);
      file_close(file);
       goto done;
   }

  // instead use the thread name to locate the file
  t->exec_file = file;
  file_deny_write(file);

  /* Read and verify executable header. */
  if (file_read (file, &ehdr, sizeof ehdr) != sizeof ehdr
      || memcmp (ehdr.e_ident, "\177ELF\1\1\1", 7)
      || ehdr.e_type != 2
      || ehdr.e_machine != 3
      || ehdr.e_version != 1
      || ehdr.e_phentsize != sizeof (struct Elf32_Phdr)
      || ehdr.e_phnum > 1024)
    {
      //printf ("load: %s: error loading executable\n", file_name);
      printf("load:%s: error loading executable\n", t->name); // instead use the thread name to locate the file
      goto done;
    }

  /* Read program headers. */
  file_ofs = ehdr.e_phoff;
  for (i = 0; i < ehdr.e_phnum; i++)
    {
      struct Elf32_Phdr phdr;

      if (file_ofs < 0 || file_ofs > file_length (file))
        goto done;
      file_seek (file, file_ofs);

      if (file_read (file, &phdr, sizeof phdr) != sizeof phdr)
        goto done;
      file_ofs += sizeof phdr;
      switch (phdr.p_type)
        {
        case PT_NULL:
        case PT_NOTE:
        case PT_PHDR:
        case PT_STACK:
        default:
          /* Ignore this segment. */
          break;
        case PT_DYNAMIC:
        case PT_INTERP:
        case PT_SHLIB:
          goto done;
        case PT_LOAD:
          if (validate_segment (&phdr, file))
            {
              bool writable = (phdr.p_flags & PF_W) != 0;
              uint32_t file_page = phdr.p_offset & ~PGMASK;
              uint32_t mem_page = phdr.p_vaddr & ~PGMASK;
              uint32_t page_offset = phdr.p_vaddr & PGMASK;
              uint32_t read_bytes, zero_bytes;
              if (phdr.p_filesz > 0)
                {
                  /* Normal segment.
                     Read initial part from disk and zero the rest. */
                  read_bytes = page_offset + phdr.p_filesz;
                  zero_bytes = (ROUND_UP (page_offset + phdr.p_memsz, PGSIZE)
                                - read_bytes);
                }
              else
                {
                  /* Entirely zero.
                     Don't read anything from disk. */
                  read_bytes = 0;
                  zero_bytes = ROUND_UP (page_offset + phdr.p_memsz, PGSIZE);
                }
              if (!load_segment_lazily(file, file_page, (void *) mem_page,
                                 read_bytes, zero_bytes, writable))
                goto done;
            }
          else
            goto done;
          break;
        }
    }

  /* Set up stack. */
  if (!setup_stack (esp, file_name))
    goto done;

  /* Start address. */
  *eip = (void (*) (void)) ehdr.e_entry;

  success = true;

 done:
  /* We arrive here whether the load is successful or not. */
  return success;
}

/* load() helpers. */

static bool install_page (void *upage, void *kpage, bool writable);

/* Checks whether PHDR describes a valid, loadable segment in
   FILE and returns true if so, false otherwise. */
static bool
validate_segment (const struct Elf32_Phdr *phdr, struct file *file)
{
  /* p_offset and p_vaddr must have the same page offset. */
  if ((phdr->p_offset & PGMASK) != (phdr->p_vaddr & PGMASK))
    return false;

  /* p_offset must point within FILE. */
  if (phdr->p_offset > (Elf32_Off) file_length (file))
    return false;

  /* p_memsz must be at least as big as p_filesz. */
  if (phdr->p_memsz < phdr->p_filesz)
    return false;

  /* The segment must not be empty. */
  if (phdr->p_memsz == 0)
    return false;

  /* The virtual memory region must both start and end within the
     user address space range. */
  if (!is_user_vaddr ((void *) phdr->p_vaddr))
    return false;
  if (!is_user_vaddr ((void *) (phdr->p_vaddr + phdr->p_memsz)))
    return false;

  /* The region cannot "wrap around" across the kernel virtual
     address space. */
  if (phdr->p_vaddr + phdr->p_memsz < phdr->p_vaddr)
    return false;

  /* Disallow mapping page 0.
     Not only is it a bad idea to map page 0, but if we allowed
     it then user code that passed a null pointer to system calls
     could quite likely panic the kernel by way of null pointer
     assertions in memcpy(), etc. */
  if (phdr->p_vaddr < PGSIZE)
    return false;

  /* It's okay. */
  return true;
}

/* Loads a segment starting at offset OFS in FILE at address
   UPAGE.  In total, READ_BYTES + ZERO_BYTES bytes of virtual
   memory are initialized, as follows:

        - READ_BYTES bytes at UPAGE must be read from FILE
          starting at offset OFS.

        - ZERO_BYTES bytes at UPAGE + READ_BYTES must be zeroed.

   The pages initialized by this function must be writable by the
   user process if WRITABLE is true, read-only otherwise.

   Return true if successful, false if a memory allocation error
   or disk read error occurs. */
static bool
load_segment (struct file *file, off_t ofs, uint8_t *upage,
              uint32_t read_bytes, uint32_t zero_bytes, bool writable)
{
  ASSERT ((read_bytes + zero_bytes) % PGSIZE == 0);
  ASSERT (pg_ofs (upage) == 0);
  ASSERT (ofs % PGSIZE == 0);

  file_seek (file, ofs);
  while (read_bytes > 0 || zero_bytes > 0)
    {
      /* Calculate how to fill this page.
         We will read PAGE_READ_BYTES bytes from FILE
         and zero the final PAGE_ZERO_BYTES bytes. */
      size_t page_read_bytes = read_bytes < PGSIZE ? read_bytes : PGSIZE;
      size_t page_zero_bytes = PGSIZE - page_read_bytes;

      /* Get a page of memory. */
      uint8_t *kpage = vm_allocate_frame(PAL_USER);
      if (kpage == NULL)
        return false;

      /* Load this page. */
      if (file_read (file, kpage, page_read_bytes) != (int) page_read_bytes)
        {
          vm_free_frame(kpage);
          return false;
        }
      memset (kpage + page_read_bytes, 0, page_zero_bytes);

      /* Add the page to the process's address space. */
      if (!install_page (upage, kpage, writable))
        {
          vm_free_frame(kpage);
          return false;
        }

      /* Advance. */
      read_bytes -= page_read_bytes;
      zero_bytes -= page_zero_bytes;
      upage += PGSIZE;
    }
  return true;
}

// load the segment in a lazy manner by performing the load from the file's offset
static bool
load_segment_lazily(struct file *file, off_t ofs, uint8_t *upage, uint32_t read_bytes, uint32_t zero_bytes, bool writable) {
    ASSERT((read_bytes + zero_bytes) % PGSIZE == 0);
    ASSERT(pg_ofs(upage) == 0);
    ASSERT(ofs % PGSIZE == 0);

    // while the page is not full...
    while (read_bytes > 0 || zero_bytes > 0) {
        // figure out how many bytes to read and how many are a placeholder
        size_t page_read_bytes = read_bytes < PGSIZE ? read_bytes : PGSIZE;
        size_t page_zero_bytes = PGSIZE - page_read_bytes;

        // add an entry to the suppl. page table based on this information
        if (!suppl_pt_insert_file (file, ofs, upage, page_read_bytes, page_zero_bytes, writable)) {
            return false;
        }

        // decrement the number of read and placeholder bytes and increment the offset and upage
        read_bytes -= page_read_bytes;
        zero_bytes -= page_zero_bytes;
        ofs += page_read_bytes;
        upage += PGSIZE; // this is Pintos-specific term that they mention is needed
    }

    return true;
}

/* Create a minimal stack by mapping a zeroed page at the top of
   user virtual memory. */
static bool
setup_stack (void **esp, const char *file_name) {
    uint8_t *kpage;
    bool success = false;

    kpage = vm_allocate_frame(PAL_USER | PAL_ZERO);
    if (kpage != NULL) {
        success = install_page (((uint8_t *) PHYS_BASE) - PGSIZE, kpage, true);
        if (success) {
            *esp = PHYS_BASE;
            uint8_t *argstr_head;
            char *command_name = thread_current()->name;
            int strlength, total_length;
            int argc;

            // push string arguments into the stack
            strlength = strlen(file_name) + 1;
            *esp -= strlength;
            //function memcpy copies the values of num bytes from the location pointed to by source directly to the memory block pointed to by destination.
            //*esp = destination
            //file_name = source
            //strlength = *esp -= strlength;  bytes to copy
            memcpy (*esp, file_name, strlength);
            total_length += strlength;

            //now push command into the stack
            strlength = strlen(command_name) + 1;
            *esp -= strlength;
            argstr_head = *esp;
            memcpy(*esp, command_name, strlength);
            total_length += strlength;

            //gets the staring address, sets the alignment and modifies esp
            *esp -= 4 - total_length % 4;
            *esp -= 4;
            * (uint32_t *) *esp = (uint32_t) NULL;

            int i = total_length - 1;
            //omits the beginning space or '\0'
            while (*(argstr_head + i) == ' '|| *(argstr_head + i) == '\0') {
                // goes through the file name and push  every last non-space and '\0' address
                if (*(argstr_head + i) == ' '){
                    *(argstr_head + i)= '\0';
                }

                i--;
            }

            char *args_string_push;
            // scan through args string and push the args address into the stack
            for (args_string_push = (char *)(argstr_head + i); i > 0; i--, args_string_push = (char*)(argstr_head + i)) {
                //first find args, if found push it's address to the stack
                if ((*args_string_push == '\0'|| *args_string_push == ' ') && (*(args_string_push + 1) != '\0' && *(args_string_push + 1) != ' ')) {
                    *esp -= 4;
                    * (uint32_t *) *esp = (uint32_t) args_string_push + 1;
                    argc++;
                }

            if (*args_string_push == ' ')
                //sets the space to '\0' to be able to terminate each arg sring
                *args_string_push = '\0';
            }

            //push command_line arg into the stack
            *esp -= 4;
            *(uint32_t *) *esp = (uint32_t) argstr_head;
            argc++;

            //push argv
            *(uint32_t *) (*esp - 4) = *(uint32_t *) esp;
            *esp -= 4;

            //push argc
            *esp -= 4;
            * (int *) *esp = argc;

            //push return address
            *esp -= 4;
            * (uint32_t *) *esp = 0x0;
        } else {
            vm_free_frame(kpage);
        }
    }

    return success;
}

/* Adds a mapping from user virtual address UPAGE to kernel
   virtual address KPAGE to the page table.
   If WRITABLE is true, the user process may modify the page;
   otherwise, it is read-only.
   UPAGE must not already be mapped.
   KPAGE should probably be a page obtained from the user pool
   with palloc_get_page().
   Returns true on success, false if UPAGE is already mapped or
   if memory allocation fails. */
static bool
install_page (void *upage, void *kpage, bool writable)
{
  struct thread *t = thread_current ();

  /* Verify that there's not already a page at that virtual
     address, then map our page there. */
  return (pagedir_get_page (t->pagedir, upage) == NULL
          && pagedir_set_page (t->pagedir, upage, kpage, writable));
}

// Custom functions for Virtual Memory

// getter for the mmfile's hash value
unsigned mmfile_hash(const struct hash_elem *p_, void *aux UNUSED) {
    const struct mmfile *p = hash_entry(p_, struct mmfile, elem);
    return hash_bytes(&p->mapid, sizeof p->mapid);
}

// compares the mapid of the lhs and the rhs and if the lhs is less than the rhs, return true
bool mmfile_less(const struct hash_elem *lhs_, const struct hash_elem *rhs_, void *aux UNUSED) {
    const struct mmfile *a = hash_entry(lhs_, struct mmfile, elem);
    const struct mmfile *b = hash_entry(rhs_, struct mmfile, elem);

    return a->mapid < b->mapid;
}

mapid_t mmfiles_insert(void *addr, struct file* file, int32_t len) {
    struct mmfile *mmf;
    mmf = calloc(1, sizeof *mmf);
    if (mmf == NULL) {
        return -1;
    }

    mmf->mapid = alloc_mapid();
    mmf->file = file;
    mmf->start_addr = addr;

    // determine how many pages we need to serve a file and then insert an entry based on that
    int offset = 0;
    int pg_cnt = 0;

    struct hash_elem *result;
    while (len > 0) {
        size_t read_bytes = len < PGSIZE ? len : PGSIZE;
        if (!suppl_pt_insert_mmf(file, offset, addr, read_bytes)) {
            return -1;
        }

        offset += PGSIZE;
        len -= PGSIZE;
        addr += PGSIZE;
        pg_cnt++;
    }

    mmf->pg_cnt = pg_cnt;

    result = hash_insert(&thread_current()->mmfiles, &mmf->elem);
    if (result != NULL) {
        return -1;
    }

    return mmf->mapid;
}

// wrapper around mmfile_free_entry
void mmfiles_remove(mapid_t mapping) {
    struct mmfile mmf;
    mmf.mapid = mapping;

    struct hash_elem *deleteable = hash_delete(&thread_current()->mmfiles, &mmf.elem);
    if (deleteable != NULL) {
        struct mmfile *mmf_ptr = hash_entry(deleteable, struct mmfile, elem);
        mmfiles_free_entry(mmf_ptr);
    }
}

// actual deallocation function
static void mmfiles_free_entry(struct mmfile* mmf_ptr) {
    int pg_cnt = mmf_ptr->pg_cnt;
    int offset = 0;

    struct suppl_pte pte;
    struct suppl_pte *pte_ptr;
    struct hash_elem *deleteable;

    // for each page, get its suppl. page table entry, checking the dirty bit to determine if it should be wrote back to the disk
    while (pg_cnt-- > 0) {
        pte.uvaddr = mmf_ptr->start_addr + offset;
        deleteable = hash_delete (&thread_current()->suppl_page_table, &pte.elem);

        if (deleteable != NULL) {
            pte_ptr = hash_entry (deleteable, struct suppl_pte, elem);
            if (pte_ptr->is_loaded && pagedir_is_dirty(thread_current()->pagedir, pte_ptr->uvaddr)) {
                /* write back to disk */
                lock_acquire (&fs_lock);
                file_seek(pte_ptr->data.mmf_page.file, pte_ptr->data.mmf_page.ofs);
                file_write(pte_ptr->data.mmf_page.file, pte_ptr->uvaddr, pte_ptr->data.mmf_page.read_bytes);
                lock_release (&fs_lock);
            }

            free(pte_ptr);
        }

        offset += PGSIZE;
    }

    lock_acquire(&fs_lock);
    file_close(mmf_ptr->file);
    lock_release(&fs_lock);

    free(mmf_ptr);
}

// assign a new mapid
static mapid_t alloc_mapid() {
    return thread_current()->mapid_allocator++;
}

// deallocate the mmfile table
void free_mmfiles(struct hash *mmfiles) {
    hash_destroy(mmfiles, free_mmfiles_entry);
}

// deallocate a single mmfile
static void free_mmfiles_entry (struct hash_elem *e, void *aux UNUSED) {
    struct mmfile *mmf = hash_entry(e, struct mmfile, elem);
    mmfiles_free_entry(mmf);
}