#![no_std]
#![allow(internal_features)]
#![feature(alloc_layout_extra)]
#![feature(allow_internal_unstable)]
#![feature(derive_coerce_pointee)]
#![feature(layout_for_ptr)]
#![feature(maybe_uninit_fill)]
#![feature(min_specialization)]
#![feature(ptr_as_uninit)]

extern crate alloc;

pub mod place;
pub use self::place::{Own, Place, Uninit};

pub mod pin;
pub use self::pin::OPin;

pub mod init;
pub use self::init::{Init, InitPin};

mod sealed {
    pub trait Sealed {}
}
