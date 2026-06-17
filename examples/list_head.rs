use std::{
    cell::Cell,
    convert::Infallible,
    marker::PhantomPinned,
    pin::Pin,
    ptr::{self, NonNull},
};

use pin_project::{pin_project, pinned_drop};
use placid::prelude::*;

#[pin_project(PinnedDrop)]
#[derive(Debug, InitPin)]
#[repr(C)]
pub struct ListHead {
    next: Link,
    prev: Link,
    #[pin]
    pin: PhantomPinned,
}

impl ListHead {
    #[inline]
    pub const fn new() -> impl InitPin<Self, Error = Infallible> {
        init_pin!(|this| ListHead {
            next: unsafe { Link::new_unchecked(this) },
            prev: unsafe { Link::new_unchecked(this) },
            #[pin]
            pin: PhantomPinned,
        })
    }

    #[inline]
    pub const fn insert_next(&self) -> impl InitPin<Self, Error = Infallible> {
        init_pin!(|this| ListHead {
            prev: (self.next.prev()).replace(unsafe { Link::new_unchecked(this) }),
            next: self.next.replace(unsafe { Link::new_unchecked(this) }),
            #[pin]
            pin: PhantomPinned,
        })
    }

    #[inline]
    pub const fn insert_prev(&self) -> impl InitPin<Self, Error = Infallible> {
        init_pin!(|this| ListHead {
            next: (self.prev.next()).replace(unsafe { Link::new_unchecked(this) }),
            prev: self.prev.replace(unsafe { Link::new_unchecked(this) }),
            #[pin]
            pin: PhantomPinned,
        })
    }

    #[inline]
    pub fn next(&self) -> Option<NonNull<Self>> {
        if ptr::eq(self.next.as_ptr(), self) {
            None
        } else {
            Some(unsafe { NonNull::new_unchecked(self.next.as_ptr() as *mut Self) })
        }
    }
}

#[pinned_drop]
impl PinnedDrop for ListHead {
    fn drop(self: Pin<&mut Self>) {
        if !ptr::eq(self.next.as_ptr(), &*self) {
            let next = unsafe { &*self.next.as_ptr() };
            let prev = unsafe { &*self.prev.as_ptr() };
            next.prev.set(&self.prev);
            prev.next.set(&self.next);
        }
    }
}

#[repr(transparent)]
#[derive(Clone, Debug)]
struct Link(Cell<NonNull<ListHead>>);

impl Link {
    /// # Safety
    ///
    /// The contents of the pointer should form a consistent circular
    /// linked list; for example, a "next" link should be pointed back
    /// by the target `ListHead`'s "prev" link and a "prev" link should be
    /// pointed back by the target `ListHead`'s "next" link.
    #[inline]
    const unsafe fn new_unchecked(ptr: NonNull<ListHead>) -> Self {
        Self(Cell::new(ptr))
    }

    #[inline]
    const fn next(&self) -> &Link {
        unsafe { &(*self.0.get().as_ptr()).next }
    }

    #[inline]
    const fn prev(&self) -> &Link {
        unsafe { &(*self.0.get().as_ptr()).prev }
    }

    #[inline]
    const fn replace(&self, other: Link) -> Link {
        unsafe { Link::new_unchecked(self.0.replace(other.0.get())) }
    }

    #[inline]
    fn set(&self, val: &Link) {
        self.0.set(val.0.get());
    }

    #[inline]
    const fn as_ptr(&self) -> *const ListHead {
        self.0.get().as_ptr()
    }
}

fn main() {
    let a = Box::pin_with(ListHead::new());
    let b = pown!(a.insert_next());
    let c = pown!(a.insert_next());
    let d = pown!(b.insert_next());
    let e = Box::pin_with(b.insert_next());
    println!("a ({a:p}): {a:?}");
    println!("b ({b:p}): {b:?}");
    println!("c ({c:p}): {c:?}");
    println!("d ({d:p}): {d:?}");
    println!("e ({e:p}): {e:?}");
    let mut inspect = &*a;
    while let Some(next) = inspect.next() {
        println!("({inspect:p}): {inspect:?}");
        inspect = unsafe { &*next.as_ptr() };
        if core::ptr::eq(inspect, &*a) {
            break;
        }
    }
}
