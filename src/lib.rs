//! # `placid` - separated ownership and in-place construction
//!
//! `placid` extends Rust's ownership model with owned and uninit references
//! with pinning variants (semantically [`&own T`], [`&uninit T`], and [`&pin
//! own T`] or `Pin<&own T>`). It also provides macros, traits, and functions
//! for constructing and manipulating these types, achieving safe [in-place
//! construction].
//!
//! ## The problem
//!
//! In Rust, the ownership of a value is typically bound to the value itself. In
//! other words, there is no way to separate the ownership of a value from it.
//!
//! This creates challenges in scenarios where:
//! - You need to construct large values in-place to build address-aware objects
//!   ergonomically;
//! - You want to transfer ownership of large objects without expensive
//!   `memcpy`s;
//!
//! Traditional Rust forces you to construct values on the stack, then move
//! them, which can be inefficient for large types (though it is able to be
//! optimized by the compiler, but it is not guaranteed). `placid` solves this
//! by introducing owned and uninit references that carry full ownership through
//! a reference.
//!
//! ## The owning reference: `&own T`
//!
//! An owned reference `&own T` is a reference that carries exclusive ownership
//! of the value it points to. Unlike `&T` or `&mut T`, an `&own T` reference
//! is responsible for dropping the value when the reference is dropped. Unlike
//! direct objects of type `T`, owned references can be moved around without
//! invalidating the place it is stored in.
//!
//! Constructing an owned reference directly on the current call stack:
//!
//! ```rust
//! use placid::{Own, own, Init, init};
//!
//! let simple = own!(42);
//! assert_eq!(*simple, 42);
//!
//! #[derive(Init)]
//! struct LargeData {
//!     buffer: [u8; 1024],
//! }
//!
//! fn process_owned(data: Own<LargeData>) {
//!     // The function owns the data and will drop it when done.
//!     println!("Processing: {} bytes", std::mem::size_of_val(&*data));
//! } // data is dropped here.
//!
//! // In a real scenario, you'd construct this in-place rather than moving.
//! let owned = own!(init!(LargeData { buffer: init::repeat(42) }));
//! process_owned(owned);
//! ```
//!
//! Moving out an owned reference from a regular smart pointer:
//!
//! ```rust
//! use placid::{Own, into_own, Place};
//!
//! let boxed = Box::new(String::from("move me"));
//!
//! let mut left; // Box<MaybeUninit<String>>
//! // Move out an owned reference from the Box. The original
//! // allocation is transferred to `left`, mutably borrowed
//! // by `own`.
//! let own = into_own!(left <- boxed);
//! assert_eq!(*own, "move me");
//!
//! // Drops the String, but not the Box allocation.
//! drop(own);
//!
//! // Now we can reuse the Box allocation.
//! let right = left.write(String::from("new value"));
//! assert_eq!(&*right, "new value");
//! ```
//!
//! ## The pinning variant: `&pin own T`
//!
//! A pinned owned reference combines the benefits of owned references with
//! pinning guarantees. This is essential for types that must not be moved
//! across places (such as self-referential structs or types with `!Unpin`). The
//! pinned owned reference ensures both exclusive ownership and address
//! stability.
//!
//! ```rust
//! use placid::{POwn, pown, InitPin, init};
//! use std::{pin::Pin, marker::PhantomPinned};
//!
//! #[derive(InitPin)]
//! struct SelfRef {
//!     data: i32,
//!     data_ptr: *const i32,
//!     marker: PhantomPinned,
//! }
//!
//! fn process_pinned(data: POwn<SelfRef>) {
//!     // The function owns the data and guarantees it won't move
//!     // This is safe because the data is pinned in place.
//!     println!("Processing pinned data");
//! } // data is dropped here, pinning guarantees are maintained.
//!
//! let pinned = pown!(
//!     // Provide initial value for the struct.
//!     init::value(SelfRef {
//!         data: 42,
//!         data_ptr: std::ptr::null(),
//!         marker: PhantomPinned,
//!     })
//!     .and_pin(|this| unsafe {
//!         // SAFETY: We are initializing the self-referential pointer.
//!         let this = Pin::into_inner_unchecked(this);
//!         this.data_ptr = &this.data as *const i32;
//!     })
//! );
//! process_pinned(pinned);
//! ```
//!
//! ### The drop guarantee
//!
//! In Rust, a pinned value must remain valid on its place until it is dropped.
//! In other words, it must be properly dropped before its place is deallocated
//! or reused. This was done naturally in its type system by binding the
//! ownership of pinned values with its place, such as the `Box::pin()` method,
//! or preventing them from getting `mem::forget`ed, such as the `pin!` macro.
//!
//! However, once the ownership is separated from the place, such as with `&pin
//! own T`, it becomes possible to accidentally forget a pinned value before the
//! place gets deallocated, thus violating the drop guarantee.
//!
//! ```ignore
//! unsafe { // Not only unsafe, but actually unsound here.
//!     let b = Box::pin(/* Some !Unpin data */);
//!     let value: &pin own T = &pin own *b;
//!     mem::forget(value);
//!
//!     // Oops! The pinned value was never
//!     // dropped even after `b` is deallocated!
//! }
//! ```
//!
//! To prevent this, `placid` enforces that the pinned value inside [`POwn<T>`]
//! is always dropped even if the `POwn<T>` itself is forgotten. This is done by
//! attaching a [drop slot] to the reference upon creation to track the drop
//! state of the pinned value. When the `POwn<T>` is dropped, the drop slot is
//! marked as dropped. If the `POwn<T>` is forgotten, the drop slot destructor
//! will drop the pinned value safely.
//!
//! That said, the drop slot itself cannot be forgotten either. Therefore,
//! manual creation of it is unsafe, and only safe method is via the
//! [`drop_slot!`] macro and its wrappers.
//!
//! ## In-place construction & `&uninit T`
//!
//! Uninit references represent writable references to uninitialized memory.
//! They are primarily used for constructing values in-place, allowing for
//! efficient initialization without unnecessary copies or moves. It combines
//! with initializers to facilitate safe and ergonomic in-place construction.
//!
//! An initializer resembles with a function typed `fn(&uninit T) -> Result<&own
//! T, E>` (or `fn(&uninit T) -> Result<&pin own T, E>` for the pinning
//! variant). It converts an uninit reference into an owned reference by
//! initializing the value in-place.
//!
//! Initializers can be composed together to build complex initialization logic.
//! See the [`Init`] and [`InitPin`] traits for more details.
//!
//! Initializers can also adopt a structural strategy by deriving the
//! [`macro@Init`] and [`macro@InitPin`] macros, which can then be constructed
//! by [`init!`] and [`init_pin!`] macros respectively. This allows for
//! declarative and ergonomic construction of complex types in-place.
//!
//! ```rust
//! use placid::{Uninit, uninit, init_pin, init, InitPin, Placed, POwn};
//! use std::{marker::PhantomPinned, pin::Pin, convert::Infallible};
//!
//! #[derive(InitPin)]
//! struct A {
//!     b: i32,
//!     c: String,
//!     marker: PhantomPinned,
//! }
//!
//! #[derive(InitPin)]
//! struct Nested {
//!     a: A,
//!     d: [u8; 1024],
//!     mid: *mut u8,
//! }
//!
//! impl Nested {
//!     pub fn new(c: &str) -> impl InitPin<Self, Error = Infallible> {
//!         init_pin!(Nested {
//!             // Nested initializers are supported.
//!             a: A {
//!                 // Values and closures are all initializers.
//!                 b: 100,
//!                 c: || c.to_string(),
//!                 marker: init::value(PhantomPinned),
//!             },
//!             // There are also a bunch of direct initializer factories.
//!             d: init::repeat(42),
//!             mid: std::ptr::null_mut(),
//!         })
//!         .and_pin(|this| unsafe {
//!             // SAFETY: We are initializing the self-referential pointer.
//!             let this = Pin::into_inner_unchecked(this);
//!             this.mid = this.d.as_mut_ptr().add(512);
//!             *this.mid = 1;
//!         })
//!     }
//!
//!     pub fn assert_values(&self, c: &str) {
//!         assert_eq!(self.a.b, 100);
//!         assert_eq!(&*self.a.c, c);
//!         assert_eq!(self.d[149], 42);
//!         assert_eq!(unsafe { *self.mid }, 1);
//!     }
//! }
//!
//! // Initialize on stack.
//! let uninit = uninit!(Nested);
//! let slot = placid::drop_slot!();
//! let pinned = uninit.write_pin(Nested::new("stack"), slot);
//! pinned.assert_values("stack");
//!
//! // Initialize in a Box.
//! let mut place = Box::<Nested>::new_uninit();
//! let uninit = Uninit::from_mut(&mut place);
//! let slot = placid::drop_slot!();
//! let pinned: POwn<Nested> = uninit.write_pin(Nested::new("boxed"), slot);
//! pinned.assert_values("boxed");
//!
//! // Convenience methods for placing initialization.
//! let pinned: Pin<Box<Nested>> =
//!     Nested::init_pin(Box::new_uninit(), Nested::new("boxed via method"));
//! pinned.assert_values("boxed via method");
//! ```
//!
//! [`&own T`]: crate::Own
//! [`&uninit T`]: crate::Uninit
//! [`&pin own T`]: crate::POwn
//! [in-place construction]: mod@crate::init
//! [place]: crate::Place
//! [drop slot]: crate::pin::DropSlot

#![no_std]
#![allow(internal_features)]
#![warn(missing_docs)]
#![cfg_attr(
    feature = "fn-impl",
    feature(tuple_trait, fn_traits, unboxed_closures, unsized_fn_params)
)]
#![feature(allocator_api)]
#![feature(allow_internal_unstable)]
#![feature(derive_coerce_pointee)]
#![feature(dropck_eyepatch)]
#![feature(maybe_uninit_fill)]
#![feature(min_specialization)]
#![feature(ptr_metadata)]

extern crate alloc;

#[cfg(test)]
extern crate std;

pub use placid_macro::{Init, InitPin, init, init_pin};

pub mod place;
pub use self::place::{Place, Placed};

pub mod owned;
pub mod pin;
pub mod uninit;
pub use self::{owned::Own, pin::POwn, uninit::Uninit};

pub mod init;
pub use self::init::{Init, InitPin};

mod sealed {
    pub trait Sealed {}
}
