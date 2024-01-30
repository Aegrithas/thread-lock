#![cfg_attr(docs_rs, feature(doc_auto_cfg))]
#![warn(missing_docs)]

//! This crate introduces the niche [`ThreadLock`] struct.
//! This struct stores arbitrary data, but only allows access to it from a specific thread at runtime; in exchange, the [`ThreadLock`] itself is [`Send`] and [`Sync`].
//! 
//! This has very limited usage, but occasionally it may be useful for cases where some parts of a struct must be multithreaded, while other parts cannot be.
//! Often, these should be split into distinct structs (one of which is [`Sync`] while the other is not), but this may occasionally be a simpler option.
//! 
//! A (contrived) example similar to an actual usage I had:
//! 
//! ```rust
//! # use std::rc::Rc;
//! # use thread_lock::ThreadLock;
//! 
//! struct A; // A: Sync
//! 
//! struct B;
//! 
//! # fn construct_ab() -> (A, Rc<B>) {
//! #   (A, Rc::new(B))
//! # }
//! # 
//! # fn do_something_with_a(a: &A) {}
//! # 
//! # fn do_something_with_b(b: &B) {}
//! # 
//! pub struct AB {
//!   
//!   a: A,
//!   b: ThreadLock<Rc<B>>
//!   
//! }
//! 
//! impl AB {
//!   
//!   pub fn new() -> Self {
//!     // note that Rc is neither Send nor Sync
//!     let (a, b): (A, Rc<B>) = construct_ab();
//!     Self { a, b: ThreadLock::new(b) }
//!   }
//!   
//!   pub fn foo(&self) { // any thread is allowed to call AB::foo
//!     do_something_with_a(&self.a);
//!   }
//!   
//!   pub fn foo_and_bar(&self) {
//!     let b = self.b.try_get().expect("foo_and_bar is only allowed on the same thread that AB was constructed");
//!     do_something_with_a(&self.a);
//!     do_something_with_b(b);
//!   }
//!   
//! }
//! ```
//! 
//! The notable features of this example:
//!   1. I want to be able to do some of the things `AB` can do on all threads, so I want `AB` to be [`Sync`].
//!   2. Some of the things AB can do (namely, `foo_and_bar`) require `AB` to have resources (namely, `B`) that cannot be shared among threads, as well as the multi-threaded resources.
//!   3. `A` and `B` can only be constructed together; this is less important, but it can make it harder or less ergonomic to split `AB` into distinct structs.

use std::{error::Error, fmt::{self, Debug, Display, Formatter}, thread::{current, ThreadId}};

/// A `ThreadLock<T>` contains a value of type `T`, but only allows access to it from one thread, checked at runtime; in exchange, every `ThreadLock<T>` is both [`Send`] and [`Sync`]
/// 
/// Logically, this can be thought of as similar to a [`RefCell`](std::cell::RefCell):
/// a [`RefCell`](std::cell::RefCell) waives (some of) the restrictions of borrow checker at compile time, but enforces them at runtime;
/// likewise, a `ThreadLock` waives (some of) the restrictions of [`Send`] and [`Sync`] as compile time, but enforces them at runtime.
/// 
/// The methods [`ThreadLock::into_inner_unlocked`], [`ThreadLock::get_unlocked`], and [`ThreadLock::get_unlocked_mut`], henceforth reffered to collectively as the `*_unlocked` methods,
/// allow users to fall back to compile-time checking of [`Send`] and [`Sync`].
/// Because of these methods, users cannot assume that other threads have not observed the value in a `ThreadLock`, unless they are certain that that value is not [`Send`]
/// (all of the `*_unlocked` methods require that the value is [`Send`]; [`ThreadLock::get_unlocked`] addionally requires that the value is [`Sync`]).
/// Users can, however, assume that the value has only been observed in ways that fulfil the contract given by the presence or absence of [`Send`] and [`Sync`] for that type.
/// 
/// # Examples
/// 
/// ```rust
/// # use std::thread;
/// # use std::sync::Arc;
/// # use thread_lock::{ThreadLock, WrongThreadError};
/// let message = 42i32; // i32 is Send and Sync, so all the `*_unlocked` methods are available
/// let locked_message = Arc::new(ThreadLock::new(message));
/// let locked_message2 = Arc::clone(&locked_message);
/// thread::spawn(move || {
///   assert_eq!(locked_message2.try_get(), Err(WrongThreadError)); // non-`*_unlocked` methods perform runtime checks, even for Send and Sync types
///   assert_eq!(locked_message2.get_unlocked(), &42);
/// });
/// assert_eq!(locked_message.try_get(), Ok(&42));
/// ```
pub struct ThreadLock<T: ?Sized> {
  
  thread: ThreadId,
  value: T
  
}

impl<T> ThreadLock<T> {
  
  /// Constructs a new `ThreadLock`, locked to the current thread; that is, only the current thread will have access to `value`.
  /// 
  /// Because this method guarantees that this `value` will not be observed on any other threads (except through the `*_unlocked` methods), `T` does not need to be `Send` or `Sync`.
  pub fn new(value: T) -> Self {
    Self { thread: current().id(), value }
  }
  
  /// Constructs a new `ThreadLock`, locked to the given thread; that is, only the given thread will have access to `value`.
  /// 
  /// Because this method can be used to move or share `value` to another thread, `T` must be `Send` and `Sync`.
  pub const fn on_thread(value: T, thread: ThreadId) -> Self where T: Send + Sync {
    Self { thread, value }
  }
  
  /// Deconstructs this `ThreadLock` and returns the contained value.
  /// 
  /// # Errors
  /// 
  /// If `self` is locked to a different thread; the error object contains `self`, so that it can be recovered if that necessary.
  pub fn try_into_inner(self) -> Result<T, TryIntoWrongThreadError<Self>> {
    if self.can_current_thread_access() {
      Ok(self.value)
    } else {
      Err(TryIntoWrongThreadError(self))
    }
  }
  
  /// Deconstructs this `ThreadLock` and returns the contained value.
  /// Equivalent to `self.try_into_inner().unwrap()`.
  /// 
  /// # Panics
  /// 
  /// If `self` is locked to a different thread.
  pub fn into_inner(self) -> T {
    self.try_into_inner().unwrap()
  }
  
  /// Deconstructs this `ThreadLock` and returns the contained value.
  /// 
  /// This methods circumvents the thread lock;
  /// that is, it allows any thread access to the underlying value, provided that that thread can prove that it is safe to move ([`Send`]) that type to other threads
  /// (as that is essentially what will happen if the thread that calls this method is not the one to which this value is locked).
  pub fn into_inner_unlocked(self) -> T where T: Send {
    self.value
  }
  
}

impl<T: ?Sized> ThreadLock<T> {
  
  /// Returns the id of the thread to which this value is locked.
  pub fn thread(&self) -> ThreadId {
    self.thread
  }
  /// Returns whether this value is locked to the current thread.
  #[inline]
  pub fn can_current_thread_access(&self) -> bool {
    self.thread == current().id()
  }
  
  /// Returns a shared reference to the underlying data.
  /// 
  /// # Errors
  /// 
  /// If the current thread does not have access to the underlying data.
  pub fn try_get(&self) -> Result<&T, WrongThreadError> {
    if self.can_current_thread_access() {
      Ok(&self.value)
    } else {
      Err(WrongThreadError)
    }
  }
  
  /// Returns a unique (mutable) reference to the underlying data.
  /// 
  /// # Errors
  /// 
  /// If the current thread does not have access to the underlying data.
  pub fn try_get_mut(&mut self) -> Result<&mut T, WrongThreadError> {
    if self.can_current_thread_access() {
      Ok(&mut self.value)
    } else {
      Err(WrongThreadError)
    }
  }
  
  /// Returns a shared reference to the underlying data.
  /// Equivalent to `self.try_get().unwrap()`
  /// 
  /// # Panics
  /// 
  /// If the current thread does not have access to the underlying data.
  pub fn get(&self) -> &T {
    self.try_get().unwrap()
  }
  
  /// Returns a unique (mutable) reference to the underlying data.
  /// Equivalent to `self.try_get_mut().unwrap()`
  /// 
  /// # Panics
  /// 
  /// If the current thread does not have access to the underlying data.
  pub fn get_mut(&mut self) -> &mut T {
    self.try_get_mut().unwrap()
  }
  
  /// Returns a shared reference to the underlying data.
  /// 
  /// This methods circumvents the thread lock;
  /// that is, it allows any thread access to the underlying value, provided that that thread can prove that it is safe to share ([`Sync`]) that type with other threads
  /// (as that is essentially what will happen if the thread that calls this method is not the one to which this value is locked).
  /// 
  /// Note that this method also requires that the value be [`Send`]; I'm not sure if this is necessary:
  /// if `T: Sync + Copy`, it can be copied onto other threads, and I'm not sure if that falls under the contract of [`Sync`], so I'm erring on the safe side.
  /// If you happen to know whether the [`Send`] bound is necessary, I would appreciate it if you would open an issue to let me know.
  pub fn get_unlocked(&self) -> &T where T: Send + Sync {
    &self.value
  }
  
  /// Returns a unique (mutable) reference to the underlying data.
  /// 
  /// This methods circumvents the thread lock;
  /// that is, it allows any thread access to the underlying value, provided that that thread can prove that it is safe to move ([`Send`]) that type to other threads
  /// (as that is essentially what will happen if the thread that calls this method is not the one to which this value is locked).
  /// 
  /// A note on the [`Send`] bound: `T` must be [`Send`] because there are ways to move data out of it, e.g. via [std::mem::replace];
  /// however, it does not need to be [`Sync`] because it takes `self` by mutable reference, which guarantees that the current thread has unique access to this `ThreadLock`, and therefore to the data contained in it.
  pub fn get_unlocked_mut(&mut self) -> &mut T where T: Send {
    &mut self.value
  }
  
}

impl<T: Default> Default for ThreadLock<T> {
  
  /// Constructs a new `ThreadLock` with the default value of `T`, locked to the current thread; cf. [`ThreadLock::new`].
  fn default() -> Self {
    Self::new(T::default())
  }
  
}

impl<T: Debug> Debug for ThreadLock<T> {
  
  /// This method will only display the underlying data if it is called from the thread to which the data is locked, so it can be called from any thread.
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    struct LockedToAnotherThread;
    impl Debug for LockedToAnotherThread {
      
      fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "<locked to another thread>")
      }
      
    }
    f
      .debug_struct("ThreadLock")
      .field("thread", &self.thread)
      .field("value", self.try_get().map_or(&LockedToAnotherThread, |value| value)) // still using the closure so that &T gets coerced to &dyn Debug
      .finish()
  }
  
}

/// SAFETY: the value of `T` can only be accessed on a single thread, regardless of which thread actually owns this lock;
/// thus, it can be safely moved around even if `T` is not [`Send`], because the `T` will never be observed on any other thread
/// (except through the `*_unlocked` methods, which do have appropriate [`Send`] and [`Sync`] bounds).
unsafe impl<T: ?Sized> Send for ThreadLock<T> {}

/// SAFETY: the value of `T` can only be accessed on a single thread, regardless of which thread owns this lock;
/// thus, it can be safely shared even if `T` is not [`Sync`], because the `T` will never be observed on any other thread
/// (except through the `*_unlocked` methods, which do have appropriate [`Send`] and [`Sync`] bounds).
unsafe impl<T: ?Sized> Sync for ThreadLock<T> {}

/// An error returned by [`ThreadLock::try_get`] and [`ThreadLock::try_get_mut`].
#[derive(Copy, Clone, Hash, Eq, PartialEq, Debug, Default)]
pub struct WrongThreadError;

impl Display for WrongThreadError {
  
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "a thread-locked object was accessed on the wrong thread")
  }
  
}

impl Error for WrongThreadError {}

/// An error returned by [`ThreadLock::try_into_inner`].
/// 
/// Spiritually equivalent to [`WrongThreadError`], but with a data field to return the [`ThreadLock`] that would otherwise be lost if a call to [`ThreadLock::try_into_inner`] failed.
#[derive(Copy, Clone, Hash, Eq, PartialEq, Default)]
pub struct TryIntoWrongThreadError<T>(pub T);

impl<T> Debug for TryIntoWrongThreadError<T> {
  
  /// Note that this method does not include any info from `self.0` so as to avoid requiring `T: Debug`.
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    f.debug_tuple("TryIntoWrongThreadError").finish()
  }
  
}

impl<T> Display for TryIntoWrongThreadError<T> {
  
  /// Note that this method does not include any info from `self.0` so as to avoid requiring `T: Display`.
  fn fmt(&self, f: &mut Formatter) -> fmt::Result {
    write!(f, "a thread-locked object was accessed on the wrong thread")
  }
  
}

impl<T> Error for TryIntoWrongThreadError<T> {}

impl<T> From<TryIntoWrongThreadError<T>> for WrongThreadError {
  
  fn from(_: TryIntoWrongThreadError<T>) -> Self {
    Self
  }
  
}