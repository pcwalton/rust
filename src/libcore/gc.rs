use io::println;
use libc::{c_char, c_int, c_uint, c_void, intptr_t, size_t, uintptr_t};
use ptr::{null, offset, to_unsafe_ptr};
use send_map::linear::LinearMap;
use sys::TypeDesc;
use unsafe::transmute;

type FreeGlue = fn(**TypeDesc, *c_void);

/**
 * Runtime structures
 *
 * NB: These must match the runtime representation.
 */

type TaskID = intptr_t;

// XXX: i386
struct Registers {
    data: [u64 * 22]
}

struct Context {
    regs: Registers,
    next: *Context,
    pad: u64
}

struct StackSegment {
    prev: *StackSegment,
    next: *StackSegment,
    end: uintptr_t,
    valgrind_id: c_uint,
    // XXX: padding on i386
    rust_task: *Task,
    canary: uintptr_t,
    data: u8
}

struct Scheduler { priv opaque: () }
struct SchedulerLoop { priv opaque: () }
struct Kernel { priv opaque: () }
struct Env { priv opaque: () }
struct AllocHeader { priv opaque: () }
struct MemoryRegion { priv opaque: () }

struct OpaqueBox {
    refcount: uint,
    tydesc: *TypeDesc,
    prev: *OpaqueBox,
    next: *OpaqueBox,
    data: u8
}

struct BoxedRegion {
    env: *Env,
    backing_region: *MemoryRegion,
    live_allocs: *OpaqueBox
}

struct Task {
    // Public fields
    refcount: intptr_t,
    id: TaskID,
    ctx: Context,
    stack_segment: *StackSegment,
    runtime_sp: uintptr_t,
    scheduler: *Scheduler,
    scheduler_loop: *SchedulerLoop,

    // Fields known only to the runtime
    kernel: *Kernel,
    name: *c_char,
    list_index: *i32,
    rendezvous_ptr: *uintptr_t,
    boxed_region: BoxedRegion
}

/**
 * Marking
 */

type MarkTable = LinearMap<uint,bool>;

unsafe fn build_mark_table(task: *Task) -> MarkTable {
    let mut table = LinearMap();
    let mut box = (*task).boxed_region.live_allocs;
    assert (*box).prev == null();
    while box != null() {
        debug!("(gc) Found box: %x", transmute(copy box));
        (&mut table).insert(transmute(copy box), false);
        box = (*box).next;
    }
    return move table;
}

unsafe fn mark_object(obj: uint, mark_table: &mut MarkTable) {
    match mark_table.find(&obj) {
        None | Some(true) => return,
        Some(false) => {}   // Continue.
    }

    let box: *OpaqueBox = transmute(copy obj);
    let size = (*(*box).tydesc).size;
    debug!("(gc) Marking %x, size %u", obj, size);
    mark_table.insert(obj, true);

    let mut ptr: *uint = transmute(&(*box).data);
    let ptr_value: uint = transmute(copy ptr);
    let mut end: *uint = transmute(ptr_value + size);
    while ptr < end {
        mark_object(*ptr, mark_table);
        ptr = offset(ptr, 1);
    }
}

unsafe fn scan_stack(task: *Task, mark_table: &mut MarkTable) {
    let mut segment = (*task).stack_segment;
    while segment != null() {
        debug!("(gc) Marking stack segment: %x-%x",
               transmute(&(*segment).data),
               (*segment).end);

        let mut ptr: *uint = transmute(&(*segment).data);
        let mut end: *uint = transmute(copy (*segment).end);
        while ptr < end {
            mark_object(*ptr, mark_table);
            ptr = offset(ptr, 1);
        }

        segment = (*segment).prev;
    }
}

unsafe fn mark(task: *Task) -> LinearMap<uint,bool> {
    let mut table = build_mark_table(task);
    scan_stack(task, &mut table);
    return table;
}

unsafe fn sweep(mark_table: &LinearMap<uint,bool>) {
    for mark_table.each_ref |root_ptr, marked| {
        if *marked { again; }

        let box: *OpaqueBox = transmute(copy *root_ptr);
        let tydesc = (*box).tydesc;
        let free_glue: FreeGlue = transmute(((*tydesc).free_glue, 0));

        debug!("(gc) Sweeping: %x, free glue: %x",
               transmute(copy box),
               (*tydesc).free_glue);

        // Call free glue.
        free_glue(to_unsafe_ptr(&tydesc), transmute(&box));

        // Free the box.
        rt::rt_free(transmute(box));
    }
}

/**
 * Entry point
 */

pub fn gc() {
    unsafe {
        let task = rust_get_task();
        let mut table = mark(task);
        sweep(&table);
    }
}

/**
 * Test
 */

fn f(n: int) {
    let _x = @42;

    if (n > 0) {
        f(n - 1);
        return;
    }

    gc();
}

struct Knot {
    mut a: Option<@Knot>;
}

fn g() {
    let knot = @Knot { a: None };
    knot.a = Some(knot);
}

fn main() {
    g();
    f(1000);
}

/**
 * Bindings to the runtime
 */

extern {
    #[rust_stack]
    /*priv*/ fn rust_get_task() -> *Task;
}

