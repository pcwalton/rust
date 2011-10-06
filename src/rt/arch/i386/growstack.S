// The stack growth stub, which Rust functions call in lieu of adjusting esp
// themselves.

#if defined(_WIN32)

#define pvArbitrary         0x14

#elif defined(__APPLE__)

#ifdef __LP64__
#define _PTHREAD_TSD_OFFSET 0x60
#else
#define _PTHREAD_TSD_OFFSET 0x48
#endif

// This is really __PTK_FRAMEWORK_GC_KEY9 for Objective-C garbage collection,
// but we steal it.
#define RUST_STACK_KEY      89

#else

// Linux doesn't use a leading _ for symbol names.
#define _rust_more_stack    rust_more_stack

#endif

// A call to this function is inserted in every function's prologue. It checks
// to see whether there's enough stack space and decrements esp. If there
// isn't enough space, bails to the runtime.
//
// Obviously, this function is performance-critical.
//
// Preconditions:
//   eax = number of bytes to allocate
//   ecx = number of bytes of params (to copy over in the allocation path).

.globl __growstack
__growstack:

    // First, find the thread-local storage.
#if defined(_WIN32)
    movl %fs:(pvArbitrary),%edx                 // edx = stack limit
#elif defined(__APPLE__)
    movl %gs:(_PTHREAD_TSD_OFFSET+4*RUST_STACK_KEY),%edx  // edx = stack limit
#elif defined(__linux__)
    movl %gs:(rust_stack_limit@INDNTPOFF),%edx  // edx = stack limit
#endif

    // Do the stack manipulation.
    subl %eax,%esp
    cmpl %edx,%esp
    jl bail
    ret

    // We're out of stack space.
bail:
    addl %eax,%esp                              // Undo the stack growth.
    pushl %ecx
    pushl %eax
    calll _rust_more_stack
    retl $8

