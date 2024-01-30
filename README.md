This crate introduces the niche `ThreadLock` struct.
This struct stores arbitrary data, but only allows access to it from a specific thread at runtime; in exchange, the `ThreadLock` itself is `Send` and `Sync`.

This has very limited usage, but occasionally it may be useful for cases where some parts of a struct must be multithreaded, while other parts cannot be.
Often, these should be split into distinct structs (one of which is `Sync` while the other is not), but this may occasionally be a simpler option.

A (contrived) example similar to an actual usage I had:

```rust
struct A; // A: Sync

struct B;

impl !Sync for B {}

pub struct AB {
  
  a: A,
  b: ThreadLock<B>
  
}

impl AB {
  
  pub fn new() -> Self {
    let (a, b): (A, B) = construct_ab();
    Self { a, b: ThreadLock::new(b) }
  }
  
  pub fn foo(&self) { // any thread is allowed to call AB::foo
    do_something_with_a(&self.a);
  }
  
  pub fn foo_and_bar(&self) {
    let b = self.b.try_get().expect("foo_and_bar is only allowed on the same thread that AB was constructed");
    do_something_with_a(&self.a);
    do_something_with_b(b);
  }
  
}
```

The notable features of this example:
  1. I want to be able to do some of the things `AB` can do on all threads, so I want `AB` to be `Sync`.
  2. Some of the things AB can do (namely, `foo_and_bar`) require `AB` to have resources (namely, `B`) that cannot be shared among threads, as well as the multi-threaded resources.
  3. `A` and `B` can only be constructed together; this is less important, but it can make it harder or less ergonomic to split `AB` into distinct structs.