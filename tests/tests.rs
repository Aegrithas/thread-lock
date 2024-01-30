use std::{cell::Cell, rc::Rc, thread, fmt::Write as _};

use thread_lock::{ThreadLock, WrongThreadError};

// In most of the tests, this does nothing but explicitly notate that the relevant type is Send
fn assert_send<T: Send>(value: T) -> T {
  value
}

// In most of the tests, this does nothing but explicitly notate that the relevant type is Send and Sync
fn assert_send_sync<T: Send + Sync>(value: T) -> T {
  value
}

#[test]
fn send_sync() {
  assert_send_sync(ThreadLock::new(Rc::new(42))); // Rc is neither Send nor Sync; this test is to "prove" that ThreadLock circumvents that
}

#[test]
fn id() {
  let lock1 = ThreadLock::new(0);
  assert_eq!(lock1.thread(), thread::current().id());
  assert!(lock1.can_current_thread_access());
  let lock2 = thread::spawn(move || {
    let lock2 = ThreadLock::new(1);
    assert_eq!(lock2.thread(), thread::current().id());
    assert!(lock2.can_current_thread_access());
    lock2
  }).join().unwrap();
  assert_ne!(lock2.thread(), thread::current().id());
  assert!(!lock2.can_current_thread_access());
}

#[test]
fn on_thread() {
  let main_id = thread::current().id();
  let lock = thread::spawn(move || {
    let lock = ThreadLock::on_thread(0, main_id);
    assert_ne!(lock.thread(), thread::current().id());
    assert!(!lock.can_current_thread_access());
    lock
  }).join().unwrap();
  assert_eq!(lock.thread(), thread::current().id());
  assert!(lock.can_current_thread_access());
}

#[test]
fn try_into_inner_success() {
  let lock = ThreadLock::new(42);
  let result = lock.try_into_inner();
  // map_err because ThreadLock<_> does not implement PartialEq, so TryIntoWrongThreadError<ThreadLock<_>> also does not
  assert_eq!(result.map_err(WrongThreadError::from), Ok(42));
}

#[test]
fn try_into_inner_failure() {
  let lock = ThreadLock::new(42);
  thread::spawn(move || {
    let result = lock.try_into_inner();
    // map_err because ThreadLock<_> does not implement PartialEq, so TryIntoWrongThreadError<ThreadLock<_>> also does not
    assert_eq!(result.map_err(WrongThreadError::from), Err(WrongThreadError));
  }).join().unwrap();
}

#[test]
fn into_inner_success() {
  let lock = ThreadLock::new(42);
  let result = lock.into_inner();
  assert_eq!(result, 42);
}

#[test]
#[should_panic]
fn into_inner_failure() {
  let lock = ThreadLock::new(42);
  thread::spawn(move || {
    let _result = lock.into_inner(); // should panic
  }).join().unwrap();
}

#[test]
fn into_inner_unlocked_success() {
  let lock1 = ThreadLock::new(assert_send(42));
  let result1 = lock1.into_inner_unlocked();
  assert_eq!(result1, 42);
  
  let lock2 = ThreadLock::new(assert_send(42));
  thread::spawn(move || {
    let result2 = lock2.into_inner_unlocked();
    assert_eq!(result2, 42);
  }).join().unwrap();
  
  let lock3 = ThreadLock::new(assert_send(Cell::new(42))); // Cell<i32> is Send, but not Sync
  thread::spawn(move || {
    let result3 = lock3.into_inner_unlocked();
    assert_eq!(result3, Cell::new(42));
  }).join().unwrap();
}

#[test]
fn try_get_success() {
  let lock = ThreadLock::new(42);
  let result = lock.try_get();
  assert_eq!(result, Ok(&42));
}

#[test]
fn try_get_failure() {
  let lock = ThreadLock::new(42);
  thread::spawn(move || {
    let result = lock.try_get();
    assert_eq!(result, Err(WrongThreadError));
  }).join().unwrap();
}

#[test]
fn get_success() {
  let lock = ThreadLock::new(42);
  let result = lock.get();
  assert_eq!(result, &42);
}

#[test]
#[should_panic]
fn get_failure() {
  let lock = ThreadLock::new(42);
  thread::spawn(move || {
    let _result = lock.get(); // should panic
  }).join().unwrap();
}

#[test]
fn get_unlocked_success() {
  let lock1 = ThreadLock::new(assert_send_sync(42));
  let result1 = lock1.get_unlocked();
  assert_eq!(result1, &42);
  
  let lock2 = ThreadLock::new(assert_send_sync(42));
  thread::spawn(move || {
    let result2 = lock2.get_unlocked();
    assert_eq!(result2, &42);
  }).join().unwrap();
}

#[test]
fn try_get_mut_success() {
  let mut lock = ThreadLock::new(42);
  let result = lock.try_get_mut();
  assert_eq!(result, Ok(&mut 42));
}

#[test]
fn try_get_mut_failure() {
  let mut lock = ThreadLock::new(42);
  thread::spawn(move || {
    let result = lock.try_get_mut();
    assert_eq!(result, Err(WrongThreadError));
  }).join().unwrap();
}

#[test]
fn get_mut_success() {
  let mut lock = ThreadLock::new(42);
  let result = lock.get_mut();
  assert_eq!(result, &mut 42);
}

#[test]
#[should_panic]
fn get_mut_failure() {
  let mut lock = ThreadLock::new(42);
  thread::spawn(move || {
    let _result = lock.get_mut(); // should panic
  }).join().unwrap();
}

#[test]
fn get_unlocked_mut_success() {
  let mut lock1 = ThreadLock::new(assert_send(42));
  let result1 = lock1.get_unlocked_mut();
  assert_eq!(result1, &mut 42);
  
  let mut lock2 = ThreadLock::new(assert_send(42));
  thread::spawn(move || {
    let result2 = lock2.get_unlocked_mut();
    assert_eq!(result2, &mut 42);
  }).join().unwrap();
  
  let mut lock3 = ThreadLock::new(assert_send(Cell::new(42))); // Cell<i32> is Send, but not Sync
  thread::spawn(move || {
    let result3 = lock3.get_unlocked_mut();
    assert_eq!(result3, &mut Cell::new(42));
  }).join().unwrap();
}

#[test]
fn default() {
  let lock: ThreadLock<bool> = Default::default();
  assert_eq!(lock.try_get(), Ok(&false));
}

#[test]
fn debug() {
  // Note: do not actually use this to check in code; the exact text of INCORRECT_THREAD_STR is not part of the public API, whereas ThreadLock::can_current_thread_access is
  const CORRECT_THREAD_STR: &str = "42";
  const INCORRECT_THREAD_STR: &str = "<locked to another thread>";
  
  let lock = ThreadLock::new(42);
  let mut buf = String::new();
  write!(buf, "{lock:?}").unwrap();
  assert!(buf.contains(CORRECT_THREAD_STR));
  assert!(!buf.contains(INCORRECT_THREAD_STR));
  
  buf.clear();
  thread::spawn(move || {
    write!(buf, "{lock:?}").unwrap();
    assert!(!buf.contains(CORRECT_THREAD_STR));
    assert!(buf.contains(INCORRECT_THREAD_STR));
  }).join().unwrap();
}