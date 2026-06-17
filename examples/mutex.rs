use std::{
    cell::{Cell, UnsafeCell},
    convert::Infallible,
    marker::PhantomPinned,
    ops::{Deref, DerefMut},
    pin::Pin,
    sync::{
        Arc,
        atomic::{AtomicBool, Ordering::*},
    },
    thread::{self, Thread},
    time::Duration,
};

use placid::prelude::*;

#[allow(dead_code)]
mod list_head;
use crate::list_head::ListHead;

#[derive(Debug)]
pub struct SpinLock {
    inner: AtomicBool,
}

impl SpinLock {
    #[inline]
    pub fn acquire(&self) -> SpinLockGuard<'_> {
        while self
            .inner
            .compare_exchange(false, true, Acquire, Relaxed)
            .is_err()
        {
            while self.inner.load(Relaxed) {
                thread::yield_now();
            }
        }
        SpinLockGuard(self)
    }

    #[inline]
    #[allow(clippy::new_without_default)]
    pub const fn new() -> Self {
        Self { inner: AtomicBool::new(false) }
    }
}

pub struct SpinLockGuard<'a>(&'a SpinLock);

impl Drop for SpinLockGuard<'_> {
    #[inline]
    fn drop(&mut self) {
        self.0.inner.store(false, Release);
    }
}

#[derive(Debug, InitPin)]
struct Mutex<T: ?Sized> {
    #[pin]
    wait_list: ListHead,
    spin_lock: SpinLock,
    locked: Cell<bool>,
    #[pin]
    data: UnsafeCell<T>,
}

unsafe impl<T: ?Sized + Send> Send for Mutex<T> {}
unsafe impl<T: ?Sized + Send> Sync for Mutex<T> {}

impl<T: ?Sized> Mutex<T> {
    #[inline]
    pub const fn new<I, M>(data: I) -> impl InitPin<Self, Error = I::Error>
    where
        I: IntoInitPin<T, M, Error: From<Infallible>>,
    {
        init_pin!(
            #[err_into(I::Error)]
            Mutex {
                #[pin]
                wait_list: ListHead::new(),
                spin_lock: SpinLock::new(),
                locked: Cell(false),
                #[pin]
                data: UnsafeCell(data),
            }
        )
    }

    pub fn lock(&self) -> Pin<MutexGuard<'_, T>> {
        let mut wait_guard = self.spin_lock.acquire();
        if self.locked.get() {
            let _entry = pown!(WaitEntry::new(&self.wait_list));
            while self.locked.get() {
                drop(wait_guard);
                thread::park();
                wait_guard = self.spin_lock.acquire();
            }
        }

        self.locked.set(true);
        unsafe { Pin::new_unchecked(MutexGuard { mutex: self, _pin: PhantomPinned }) }
    }

    #[inline]
    #[allow(dead_code)]
    pub fn get_pin_mut(self: Pin<&mut Self>) -> Pin<&mut T> {
        unsafe { self.map_unchecked_mut(|s| &mut *s.data.get()) }
    }
}

pub struct MutexGuard<'a, T: ?Sized> {
    mutex: &'a Mutex<T>,
    _pin: PhantomPinned,
}

impl<'a, T: ?Sized> Deref for MutexGuard<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mutex.data.get() }
    }
}

impl<'a, T: ?Sized> DerefMut for MutexGuard<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.mutex.data.get() }
    }
}

impl<'a, T: ?Sized> Drop for MutexGuard<'a, T> {
    fn drop(&mut self) {
        let _wait_guard = self.mutex.spin_lock.acquire();
        self.mutex.locked.set(false);

        if let Some(entry) = self.mutex.wait_list.next() {
            unsafe { entry.cast::<WaitEntry>().as_ref().thread.unpark() };
        }
    }
}

#[derive(Debug, InitPin)]
#[repr(C)]
struct WaitEntry {
    #[pin]
    list: ListHead,
    thread: Thread,
}

impl WaitEntry {
    #[inline]
    const fn new(list: &ListHead) -> impl InitPin<Self, Error = Infallible> {
        init_pin!(WaitEntry {
            thread: thread::current(),
            #[pin]
            list: list.insert_prev(),
        })
    }
}

fn main() {
    let mtx: Pin<Arc<Mutex<usize>>> = Arc::pin_with(Mutex::new(0));
    let mut handles = vec![];
    let thread_count = 20;
    let workload = if cfg!(miri) { 100 } else { 1_000 };
    for i in 0..thread_count {
        let mtx = mtx.clone();
        handles.push(
            thread::Builder::new()
                .name(format!("worker #{i}"))
                .spawn(move || {
                    for _ in 0..workload {
                        *mtx.lock() += 1;
                    }
                    println!("{i} halfway");
                    thread::sleep(Duration::from_millis((i as u64) * 10));
                    for _ in 0..workload {
                        *mtx.lock() += 1;
                    }
                    println!("{i} finished");
                })
                .expect("should not fail"),
        );
    }
    for h in handles {
        h.join().expect("thread panicked");
    }
    println!("{:?}", *mtx.lock());
    assert_eq!(*mtx.lock(), workload * thread_count * 2);
}
