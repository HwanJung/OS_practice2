#include "types.h"
#include "param.h"
#include "memlayout.h"
#include "riscv.h"
#include "spinlock.h"
#include "proc.h"
#include "defs.h"

struct cpu cpus[NCPU];

struct proc proc[NPROC];

struct proc *initproc;

int nextpid = 1;
struct spinlock pid_lock;

extern void forkret(void);
static void freeproc(struct proc *p);

extern char trampoline[]; // trampoline.S

// helps ensure that wakeups of wait()ing
// parents are not lost. helps obey the
// memory model when using p->parent.
// must be acquired before any p->lock.
struct spinlock wait_lock;

enum schedulermode schedmode;
struct spinlock schedmode_lock;

struct queue fcfs_queue;
struct queue mlfq_queue[6]; // 0 : L0, 1 : L1, 2 ~ 5 : L2(priority 3 ~ 0)
struct spinlock fcfs_queue_lock;
struct spinlock mlfq_queue_lock;


int tickcount = 0;
struct spinlock tickcount_lock;

void
fcfs_init(void)
{
  initlock(&fcfs_queue_lock, "fcfs_queue_lock");
  fcfs_queue.front = 0;
  fcfs_queue.rear = -1;
  fcfs_queue.size = 0;
}

void
mlfq_init(void)
{
  initlock(&mlfq_queue_lock, "mlfq_queue_lock");
  for(int i = 0; i < 6; i++) {
    mlfq_queue[i].front = 0;
    mlfq_queue[i].rear = -1;
    mlfq_queue[i].size = 0;
  }
}

void 
fcfs_enqueue(struct proc *p)
{
  acquire(&fcfs_queue_lock);
  if(fcfs_queue.size == NPROC) {
    release(&fcfs_queue_lock);
    panic("FCFS queue is full");
  }
  fcfs_queue.rear = (fcfs_queue.rear + 1) % NPROC;
  fcfs_queue.proc[fcfs_queue.rear] = p;
  fcfs_queue.size++;
  release(&fcfs_queue_lock);

  // printf("Equeued PID %d (level=%d, priority=%d, state=%d)\n", p->pid, p->level, p->priority, p->state);

}

// Before call mlfq_enqueue, p lock need
void
mlfq_enqueue(struct proc *p)
{
  int queueidx = p->level;

  if(p->priority < 3) {
    queueidx = 5 - p->priority; // idx will be 3 ~ 5
  }

  acquire(&mlfq_queue_lock);

  if(mlfq_queue[queueidx].size == NPROC) {
    release(&mlfq_queue_lock);
    panic("MLFQ queue is full");
  }

  mlfq_queue[queueidx].rear = (mlfq_queue[queueidx].rear + 1) % NPROC;
  mlfq_queue[queueidx].proc[mlfq_queue[queueidx].rear] = p;
  mlfq_queue[queueidx].size++;

  release(&mlfq_queue_lock);

  // printf("Equeued PID %d (level=%d, priority=%d, state=%d)\n", p->pid, p->level, p->priority, p->state);

}

struct proc*
fcfs_dequeue(void)
{
  acquire(&fcfs_queue_lock);

  if(fcfs_queue.size == 0) {
    release(&fcfs_queue_lock);
    panic("FCFS queue is empty");
  }

  struct proc *p = fcfs_queue.proc[fcfs_queue.front];
  fcfs_queue.front = (fcfs_queue.front + 1) % NPROC;
  fcfs_queue.size--;
  release(&fcfs_queue_lock);

  return p;
}

struct proc*
mlfq_dequeue(void)
{
  for(int i = 0; i < 6; i++) {
    acquire(&mlfq_queue_lock);

    if(mlfq_queue[i].size > 0) {
      struct proc *p = mlfq_queue[i].proc[mlfq_queue[i].front];
      mlfq_queue[i].front = (mlfq_queue[i].front + 1) % NPROC;
      mlfq_queue[i].size--;

      release(&mlfq_queue_lock);

      return p;
    }
    release(&mlfq_queue_lock);
  }

  panic("MLFQ queue is empty");
}

void 
enqueue(struct proc *p)
{
  acquire(&schedmode_lock);
  enum schedulermode mode = schedmode;
  release(&schedmode_lock);

  if(mode == FCFS) {
    p->level = -1;
    p->priority = -1;
    p->timequantum = -1;
    fcfs_enqueue(p);
  } else if(mode == MLFQ) {
    p->level = 0;
    p->priority = 3;
    p->timequantum = 2 * p->level + 1;
    mlfq_enqueue(p);
  } else {
    panic("Unknown scheduling mode");
  } 
}

struct proc*
dequeue(void)
{
  acquire(&schedmode_lock);
  enum schedulermode mode = schedmode;
  release(&schedmode_lock);

  if(mode == FCFS) {
    return fcfs_dequeue();
  } else if(mode == MLFQ) {
    return mlfq_dequeue();
  } else {
    panic("Unknown scheduling mode");
  }
}

int isEmptyfcfsQueue()
{
  acquire(&fcfs_queue_lock);
  int empty = fcfs_queue.size == 0;
  release(&fcfs_queue_lock);
  return empty;
}

int isEmptymlfqQueue()
{
  int empty = 1;

  acquire(&mlfq_queue_lock);
  for(int i = 0; i < 6; i++) {
    if(mlfq_queue[i].size > 0) {
      empty = 0;
      break;
    }
  }
  release(&mlfq_queue_lock);

  return empty;
}

int
isEmptyQueue()
{
  acquire(&schedmode_lock);
  enum schedulermode mode = schedmode;
  release(&schedmode_lock);

  int empty = 0;

  if(mode == FCFS) {
    empty = isEmptyfcfsQueue();
  } else if(mode == MLFQ) {
    empty = isEmptymlfqQueue();
  }

  return empty;
}

void priorityboost(){
  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if(!(p->state == UNUSED && p->state == ZOMBIE)) {
      p->level = 0;
      p->priority = 3;
      p->timequantum = 2 * p->level + 1;

    }
    release(&p->lock);
  }

  for(int i = 1; i < 6; i++){
    while(mlfq_queue[i].size != 0){
      enqueue(mlfq_queue[i].proc[mlfq_queue[i].front]);
      mlfq_queue[i].front = (mlfq_queue[i].front + 1) % NPROC;
      mlfq_queue[i].size--;
    }
  }
}

void
receiveTimerIntr(void)
{
  acquire(&schedmode_lock);
  enum schedulermode mode = schedmode;
  release(&schedmode_lock);

  if(mode == MLFQ) {
    acquire(&tickcount_lock);
    tickcount++;
    if(tickcount == 50){
      tickcount = 0;
      release(&tickcount_lock);
      priorityboost();
      return;
    }
    release(&tickcount_lock);

    struct proc *p = myproc();

    acquire(&p->lock);
    p->timequantum--;

    if(p->timequantum == 0) {
      if(p->level < 2) {
        p->level++;
      } else {
        p->priority = (p->priority == 0) ? 0 : p->priority - 1;
      }
      p->timequantum = 2 * p->level + 1;
      
      release(&p->lock);

      yield();
    } else {
      release(&p->lock);
    }
  }
}



// Allocate a page for each process's kernel stack.
// Map it high in memory, followed by an invalid
// guard page.
void
proc_mapstacks(pagetable_t kpgtbl)
{
  struct proc *p;
  
  for(p = proc; p < &proc[NPROC]; p++) {
    char *pa = kalloc();
    if(pa == 0)
      panic("kalloc");
    uint64 va = KSTACK((int) (p - proc));
    kvmmap(kpgtbl, va, (uint64)pa, PGSIZE, PTE_R | PTE_W);
  }
}

// initialize the proc table.
void
procinit(void)
{
  struct proc *p;
  
  initlock(&pid_lock, "nextpid");
  initlock(&wait_lock, "wait_lock");
  for(p = proc; p < &proc[NPROC]; p++) {
      initlock(&p->lock, "proc");
      p->state = UNUSED;
      p->kstack = KSTACK((int) (p - proc));
  }

  schedmode = FCFS;
  fcfs_init();
  mlfq_init();
}

// Must be called with interrupts disabled,
// to prevent race with process being moved
// to a different CPU.
int
cpuid()
{
  int id = r_tp();
  return id;
}

// Return this CPU's cpu struct.
// Interrupts must be disabled.
struct cpu*
mycpu(void)
{
  int id = cpuid();
  struct cpu *c = &cpus[id];
  return c;
}

// Return the current struct proc *, or zero if none.
struct proc*
myproc(void)
{
  push_off();
  struct cpu *c = mycpu();
  struct proc *p = c->proc;
  pop_off();
  return p;
}

int
allocpid()
{
  int pid;
  
  acquire(&pid_lock);
  pid = nextpid;
  nextpid = nextpid + 1;
  release(&pid_lock);

  return pid;
}

// Look in the process table for an UNUSED proc.
// If found, initialize state required to run in the kernel,
// and return with p->lock held.
// If there are no free procs, or a memory allocation fails, return 0.
static struct proc*
allocproc(void)
{
  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if(p->state == UNUSED) {
      goto found;
    } else {
      release(&p->lock);
    }
  }
  return 0;

found:
  p->pid = allocpid();
  p->state = USED;
  p->creationtime = ticks;

  // Allocate a trapframe page.
  if((p->trapframe = (struct trapframe *)kalloc()) == 0){
    freeproc(p);
    release(&p->lock);
    return 0;
  }

  // An empty user page table.
  p->pagetable = proc_pagetable(p);
  if(p->pagetable == 0){
    freeproc(p);
    release(&p->lock);
    return 0;
  }

  // Set up new context to start executing at forkret,
  // which returns to user space.
  memset(&p->context, 0, sizeof(p->context));
  p->context.ra = (uint64)forkret;
  p->context.sp = p->kstack + PGSIZE;

  return p;
}

// free a proc structure and the data hanging from it,
// including user pages.
// p->lock must be held.
static void
freeproc(struct proc *p)
{
  if(p->trapframe)
    kfree((void*)p->trapframe);
  p->trapframe = 0;
  if(p->pagetable)
    proc_freepagetable(p->pagetable, p->sz);
  p->pagetable = 0;
  p->sz = 0;
  p->pid = 0;
  p->parent = 0;
  p->name[0] = 0;
  p->chan = 0;
  p->killed = 0;
  p->xstate = 0;
  p->state = UNUSED;
}

// Create a user page table for a given process, with no user memory,
// but with trampoline and trapframe pages.
pagetable_t
proc_pagetable(struct proc *p)
{
  pagetable_t pagetable;

  // An empty page table.
  pagetable = uvmcreate();
  if(pagetable == 0)
    return 0;

  // map the trampoline code (for system call return)
  // at the highest user virtual address.
  // only the supervisor uses it, on the way
  // to/from user space, so not PTE_U.
  if(mappages(pagetable, TRAMPOLINE, PGSIZE,
              (uint64)trampoline, PTE_R | PTE_X) < 0){
    uvmfree(pagetable, 0);
    return 0;
  }

  // map the trapframe page just below the trampoline page, for
  // trampoline.S.
  if(mappages(pagetable, TRAPFRAME, PGSIZE,
              (uint64)(p->trapframe), PTE_R | PTE_W) < 0){
    uvmunmap(pagetable, TRAMPOLINE, 1, 0);
    uvmfree(pagetable, 0);
    return 0;
  }

  return pagetable;
}

// Free a process's page table, and free the
// physical memory it refers to.
void
proc_freepagetable(pagetable_t pagetable, uint64 sz)
{
  uvmunmap(pagetable, TRAMPOLINE, 1, 0);
  uvmunmap(pagetable, TRAPFRAME, 1, 0);
  uvmfree(pagetable, sz);
}

// a user program that calls exec("/init")
// assembled from ../user/initcode.S
// od -t xC ../user/initcode
uchar initcode[] = {
  0x17, 0x05, 0x00, 0x00, 0x13, 0x05, 0x45, 0x02,
  0x97, 0x05, 0x00, 0x00, 0x93, 0x85, 0x35, 0x02,
  0x93, 0x08, 0x70, 0x00, 0x73, 0x00, 0x00, 0x00,
  0x93, 0x08, 0x20, 0x00, 0x73, 0x00, 0x00, 0x00,
  0xef, 0xf0, 0x9f, 0xff, 0x2f, 0x69, 0x6e, 0x69,
  0x74, 0x00, 0x00, 0x24, 0x00, 0x00, 0x00, 0x00,
  0x00, 0x00, 0x00, 0x00
};

// Set up first user process.
void
userinit(void)
{
  struct proc *p;

  p = allocproc();
  initproc = p;
  
  // allocate one user page and copy initcode's instructions
  // and data into it.
  uvmfirst(p->pagetable, initcode, sizeof(initcode));
  p->sz = PGSIZE;

  // prepare for the very first "return" from kernel to user.
  p->trapframe->epc = 0;      // user program counter
  p->trapframe->sp = PGSIZE;  // user stack pointer

  safestrcpy(p->name, "initcode", sizeof(p->name));
  p->cwd = namei("/");

  p->state = RUNNABLE;

  enqueue(p);

  release(&p->lock);
}

// Grow or shrink user memory by n bytes.
// Return 0 on success, -1 on failure.
int
growproc(int n)
{
  uint64 sz;
  struct proc *p = myproc();

  sz = p->sz;
  if(n > 0){
    if((sz = uvmalloc(p->pagetable, sz, sz + n, PTE_W)) == 0) {
      return -1;
    }
  } else if(n < 0){
    sz = uvmdealloc(p->pagetable, sz, sz + n);
  }
  p->sz = sz;
  return 0;
}

// Create a new process, copying the parent.
// Sets up child kernel stack to return as if from fork() system call.
int
fork(void)
{
  int i, pid;
  struct proc *np;
  struct proc *p = myproc();

  // Allocate process.
  if((np = allocproc()) == 0){
    return -1;
  }

  // Copy user memory from parent to child.
  if(uvmcopy(p->pagetable, np->pagetable, p->sz) < 0){
    freeproc(np);
    release(&np->lock);
    return -1;
  }
  np->sz = p->sz;

  // copy saved user registers.
  *(np->trapframe) = *(p->trapframe);

  // Cause fork to return 0 in the child.
  np->trapframe->a0 = 0;

  // increment reference counts on open file descriptors.
  for(i = 0; i < NOFILE; i++)
    if(p->ofile[i])
      np->ofile[i] = filedup(p->ofile[i]);
  np->cwd = idup(p->cwd);

  safestrcpy(np->name, p->name, sizeof(p->name));

  pid = np->pid;

  release(&np->lock);

  acquire(&wait_lock);
  np->parent = p;
  release(&wait_lock);

  acquire(&np->lock);
  np->state = RUNNABLE;
  enqueue(np);
  release(&np->lock);

  return pid;
}

// Pass p's abandoned children to init.
// Caller must hold wait_lock.
void
reparent(struct proc *p)
{
  struct proc *pp;

  for(pp = proc; pp < &proc[NPROC]; pp++){
    if(pp->parent == p){
      pp->parent = initproc;
      wakeup(initproc);
    }
  }
}

// Exit the current process.  Does not return.
// An exited process remains in the zombie state
// until its parent calls wait().
void
exit(int status)
{
  struct proc *p = myproc();

  if(p == initproc)
    panic("init exiting");

  // Close all open files.
  for(int fd = 0; fd < NOFILE; fd++){
    if(p->ofile[fd]){
      struct file *f = p->ofile[fd];
      fileclose(f);
      p->ofile[fd] = 0;
    }
  }

  begin_op();
  iput(p->cwd);
  end_op();
  p->cwd = 0;

  acquire(&wait_lock);

  // Give any children to init.
  reparent(p);

  // Parent might be sleeping in wait().
  wakeup(p->parent);
  
  acquire(&p->lock);

  p->xstate = status;
  p->state = ZOMBIE;

  release(&wait_lock);

  // Jump into the scheduler, never to return.
  sched();
  panic("zombie exit");
}

// Wait for a child process to exit and return its pid.
// Return -1 if this process has no children.
int
wait(uint64 addr)
{
  struct proc *pp;
  int havekids, pid;
  struct proc *p = myproc();

  acquire(&wait_lock);

  for(;;){
    // Scan through table looking for exited children.
    havekids = 0;
    for(pp = proc; pp < &proc[NPROC]; pp++){
      if(pp->parent == p){
        // make sure the child isn't still in exit() or swtch().
        acquire(&pp->lock);

        havekids = 1;
        if(pp->state == ZOMBIE){
          // Found one.
          pid = pp->pid;
          if(addr != 0 && copyout(p->pagetable, addr, (char *)&pp->xstate,
                                  sizeof(pp->xstate)) < 0) {
            release(&pp->lock);
            release(&wait_lock);
            return -1;
          }
          freeproc(pp);
          release(&pp->lock);
          release(&wait_lock);
          return pid;
        }
        release(&pp->lock);
      }
    }

    // No point waiting if we don't have any children.
    if(!havekids || killed(p)){
      release(&wait_lock);
      return -1;
    }
    
    // Wait for a child to exit.
    sleep(p, &wait_lock);  //DOC: wait-sleep
  }
}

// Per-CPU process scheduler.
// Each CPU calls scheduler() after setting itself up.
// Scheduler never returns.  It loops, doing:
//  - choose a process to run.
//  - swtch to start running that process.
//  - eventually that process transfers control
//    via swtch back to the scheduler.
void
scheduler(void)
{
  struct proc *p;
  struct cpu *c = mycpu();
  
  c->proc = 0;
  for(;;){
    // The most recent process to run may have had interrupts
    // turned off; enable them to avoid a deadlock if all
    // processes are waiting.
    intr_on();
    
    if(isEmptyQueue()){
      asm volatile("wfi");
      continue;
    }

    p = dequeue();
    acquire(&p->lock);
    // printf("[scheduler] Dequeued PID %d (level=%d, priority=%d)\n", p->pid, p->level, p->priority);
    p->state = RUNNING;
    c->proc = p;
    swtch(&c->context, &p->context);

    c->proc = 0;
    release(&p->lock);
  }
}

// Switch to scheduler.  Must hold only p->lock
// and have changed proc->state. Saves and restores
// intena because intena is a property of this
// kernel thread, not this CPU. It should
// be proc->intena and proc->noff, but that would
// break in the few places where a lock is held but
// there's no process.
void
sched(void)
{
  int intena;
  struct proc *p = myproc();

  if(!holding(&p->lock))
    panic("sched p->lock");
  if(mycpu()->noff != 1)
    panic("sched locks");
  if(p->state == RUNNING)
    panic("sched running");
  if(intr_get())
    panic("sched interruptible");

  intena = mycpu()->intena;
  swtch(&p->context, &mycpu()->context);
  mycpu()->intena = intena;
}

// Give up the CPU for one scheduling round.
void
yield(void)
{
  struct proc *p = myproc();

  acquire(&schedmode_lock);
  int mode = schedmode;
  release(&schedmode_lock);

  acquire(&p->lock);
  p->state = RUNNABLE;
  if(mode == FCFS){
    //printf("yield process %d, level : %d, priority : %d\n", p->pid, p->level, p->priority);
    
    fcfs_enqueue(p);
  } else if(schedmode == MLFQ){
    mlfq_enqueue(p);
  }
  sched();
  release(&p->lock);
}

// A fork child's very first scheduling by scheduler()
// will swtch to forkret.
void
forkret(void)
{
  static int first = 1;

  // Still holding p->lock from scheduler.
  release(&myproc()->lock);

  if (first) {
    // File system initialization must be run in the context of a
    // regular process (e.g., because it calls sleep), and thus cannot
    // be run from main().
    fsinit(ROOTDEV);

    first = 0;
    // ensure other cores see first=0.
    __sync_synchronize();
  }

  usertrapret();
}

// Atomically release lock and sleep on chan.
// Reacquires lock when awakened.
void
sleep(void *chan, struct spinlock *lk)
{
  struct proc *p = myproc();
  
  // Must acquire p->lock in order to
  // change p->state and then call sched.
  // Once we hold p->lock, we can be
  // guaranteed that we won't miss any wakeup
  // (wakeup locks p->lock),
  // so it's okay to release lk.

  acquire(&p->lock);  //DOC: sleeplock1
  release(lk);

  // Go to sleep.
  p->chan = chan;
  p->state = SLEEPING;

  sched();

  // Tidy up.
  p->chan = 0;

  // Reacquire original lock.
  release(&p->lock);
  acquire(lk);
}

// Wake up all processes sleeping on chan.
// Must be called without any p->lock.
void
wakeup(void *chan)
{
  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++) {
    if(p != myproc()){
      acquire(&p->lock);
      if(p->state == SLEEPING && p->chan == chan) {
        p->state = RUNNABLE;
        enqueue(p);
      }
      release(&p->lock);
    }
  }
}

// Kill the process with the given pid.
// The victim won't exit until it tries to return
// to user space (see usertrap() in trap.c).
int
kill(int pid)
{
  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++){
    acquire(&p->lock);
    if(p->pid == pid){
      p->killed = 1;
      if(p->state == SLEEPING){
        // Wake process from sleep().
        p->state = RUNNABLE;
        enqueue(p);
      }
      release(&p->lock);
      return 0;
    }
    release(&p->lock);
  }
  return -1;
}

void
setkilled(struct proc *p)
{
  acquire(&p->lock);
  p->killed = 1;
  release(&p->lock);
}

int
killed(struct proc *p)
{
  int k;
  
  acquire(&p->lock);
  k = p->killed;
  release(&p->lock);
  return k;
}

// Copy to either a user address, or kernel address,
// depending on usr_dst.
// Returns 0 on success, -1 on error.
int
either_copyout(int user_dst, uint64 dst, void *src, uint64 len)
{
  struct proc *p = myproc();
  if(user_dst){
    return copyout(p->pagetable, dst, src, len);
  } else {
    memmove((char *)dst, src, len);
    return 0;
  }
}

// Copy from either a user address, or kernel address,
// depending on usr_src.
// Returns 0 on success, -1 on error.
int
either_copyin(void *dst, int user_src, uint64 src, uint64 len)
{
  struct proc *p = myproc();
  if(user_src){
    return copyin(p->pagetable, dst, src, len);
  } else {
    memmove(dst, (char*)src, len);
    return 0;
  }
}

// Print a process listing to console.  For debugging.
// Runs when user types ^P on console.
// No lock to avoid wedging a stuck machine further.
void
procdump(void)
{
  static char *states[] = {
  [UNUSED]    "unused",
  [USED]      "used",
  [SLEEPING]  "sleep ",
  [RUNNABLE]  "runble",
  [RUNNING]   "run   ",
  [ZOMBIE]    "zombie"
  };
  struct proc *p;
  char *state;

  printf("\n");
  for(p = proc; p < &proc[NPROC]; p++){
    if(p->state == UNUSED)
      continue;
    if(p->state >= 0 && p->state < NELEM(states) && states[p->state])
      state = states[p->state];
    else
      state = "???";
    printf("%d %s %s", p->pid, state, p->name);
    printf("\n");
  }
}

// check whether a process with the pid exists
struct proc*
getprocess(int pid)
{
  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if(p->pid == pid) {
      release(&p->lock);
      return p;
    }
    release(&p->lock);
  }

  return 0;
}

// set priority of process with the pid
int setpriority(int pid, int priority)
{
  struct proc *p = getprocess(pid);
  
  if(p == 0) {
    return -1;
  }

  if(priority < 0 || priority > 3) {
    return -2;
  }

  acquire(&p->lock);
  p->priority = priority;
  // printf("pid : %d, priority : %d\n", pid, p->priority);
  release(&p->lock);

  return 0;
}

int
getlev(void)
{
  if(schedmode == FCFS) {
    return 99;
  } else {
    struct proc *p = myproc();

    acquire(&p->lock);
    int level = p->level;
    release(&p->lock);

    return level;
  }
}

int mlfqmode(void)
{
  acquire(&schedmode_lock);

  if(schedmode == MLFQ) {
    printf("Scheduling mode is already MLFQ\n");
    release(&schedmode_lock);
    return -1;
  }

  schedmode = MLFQ;
  release(&schedmode_lock);

  acquire(&tickcount_lock);
  tickcount = 0;
  release(&tickcount_lock);

  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if(!(p->state == UNUSED && p->state == ZOMBIE)) {
      p->level = 0;
      p->priority = 3;
      p->timequantum = 2 * p->level + 1;
    }
    release(&p->lock);
  }

  while(!isEmptyfcfsQueue()) {
    struct proc *p = fcfs_dequeue();
    acquire(&p->lock);
    mlfq_enqueue(p);
    release(&p->lock);
  }

  return 0;
}

int fcfsmode(void)
{
  acquire(&schedmode_lock);

  if(schedmode == FCFS) {
    printf("Scheduling mode is already FCFS\n");
    release(&schedmode_lock);
    return -1;
  }

  schedmode = FCFS;
  release(&schedmode_lock);

  struct proc *dequeuedProc[NPROC];
  int procCnt = 0;

  while(!isEmptymlfqQueue()) {
    dequeuedProc[procCnt++] = mlfq_dequeue();
  }

  struct proc *p;

  for(p = proc; p < &proc[NPROC]; p++) {
    acquire(&p->lock);
    if(!(p->state == UNUSED && p->state == ZOMBIE)) {
      p->level = -1;
      p->priority = -1;
      p->timequantum = -1;
    }
    release(&p->lock);
  }

  int isEnqueued[NPROC] = {0};

  while(1) {
    struct proc *earlyP;
    int findEarlyP = 0;
    int earlyPCreationTime = 0;
    int earlyPIdx = -1;

    for(int i = 0; i < procCnt; i++) {
      p = dequeuedProc[i];

      if(isEnqueued[i] == 1) {
        continue;
      }

      acquire(&p->lock);
      int creationTime = p->creationtime;
      release(&p->lock);

      if(findEarlyP == 0) {
        earlyP = p;
        earlyPIdx = i;
        earlyPCreationTime = creationTime;
        findEarlyP = 1;
      } else {
        if(creationTime < earlyPCreationTime) {
          earlyP = p;
          earlyPIdx = i;
          earlyPCreationTime = creationTime;
        }
      }
    }

    if(findEarlyP) {
      isEnqueued[earlyPIdx] = 1;
      acquire(&earlyP->lock);
      fcfs_enqueue(earlyP);
      release(&earlyP->lock);
    } else {
      break;
    }
  }

  return 0;
}