#![no_std]
#![allow(internal_features)]
#![warn(missing_docs)]
#![cfg_attr(
    feature = "fn-impl",
    feature(tuple_trait, fn_traits, unboxed_closures, unsized_fn_params)
)]
#![feature(alloc_layout_extra)]
#![feature(allocator_api)]
#![feature(allow_internal_unstable)]
#![feature(derive_coerce_pointee)]
#![feature(dropck_eyepatch)]
#![feature(layout_for_ptr)]
#![feature(maybe_uninit_fill)]
#![feature(min_specialization)]
#![feature(ptr_as_uninit)]
#![feature(ptr_metadata)]

//! # `placid`
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
//! ```ignore
//! use placid::{Own, own, Init, init};
//!
//! #[derive(Init)]
//! struct LargeData {
//!     buffer: [u8; 1024],
//! }
//!
//! fn process_owned(data: Own<LargeData>) {
//!     // The function owns the data and will drop it when done
//!     println!("Processing: {} bytes", std::mem::size_of_val(&*data));
//! } // data is dropped here
//!
//! // In a real scenario, you'd construct this in-place rather than moving
//! let owned = own!(init!(LargeData { buffer: init::repeat(0) }));
//! process_owned(owned);
//! ```
//!
//! ## The pinning variant: `&pin own T`
//!
//! TODO: explain pinned owned references, focusing on how the drop guarantees
//! is satisfied.
//!
//! ## In-place construction & `&uninit T`
//!
//! TODO: explain uninit references and in-place construction
//!
//! [`&own T`]: crate::Own
//! [`&uninit T`]: crate::Uninit
//! [`&pin own T`]: crate::POwn
//! [in-place construction]: crate::init
//! [place]: crate::Place

extern crate alloc;

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
