#ifndef USERPROG_SYSCALL_H
#define USERPROG_SYSCALL_H

#include "threads/thread.h"
#include "userprog/process.h"

// ensure that only one thread at a time is using the file system
struct lock fs_lock;

void syscall_init (void);
void close_file_by_owner(tid_t);
bool is_valid_ptr(const void *);

#endif /* userprog/syscall.h */