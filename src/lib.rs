#![no_std]
#![allow(internal_features)]
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

extern crate alloc;

pub use placid_macro::{Init, InitPin};

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
