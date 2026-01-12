//! Defines traits and implementations for constructing places in memory
//! with specified arguments.

use core::{alloc::Allocator, fmt, ops::Deref, pin::Pin};

use crate::{
    init::{IntoInit, IntoInitPin},
    place::Place,
};

/// A place in memory that can be created with specified arguments.
///
/// This trait is rarely used directly. Instead, use one of the more specific
/// place construction traits such as [`PlaceNew`], [`PlaceNewIn`],
/// or [`PlaceSlice`]. See the trait list in the module documentation for more
/// details.
///
/// # Arguments
///
/// `Args` is a bunch of arguments required to create the place itself,
/// unrelated to initialization of the place's content. Defaults to `()`.
pub trait PlaceConstruct<Args = ()>: Sized + Deref {
    /// The uninitialized place type that can be constructed into `Self`.
    type Uninit: Place<Self::Target, Init = Self>;
    /// The error type that can occur during construction.
    type Error: fmt::Debug;

    /// Tries to create a new uninitialized place with specified arguments.
    ///
    /// # Errors
    ///
    /// If the creation fails, this method returns an error.
    fn try_new_uninit_in(args: Args) -> Result<Self::Uninit, Self::Error>;

    /// Creates a new uninitialized place with specified arguments.
    ///
    /// # Panics
    ///
    /// This method will panic if the creation fails.
    fn new_uninit_in(args: Args) -> Self::Uninit {
        Self::try_new_uninit_in(args).expect("failed to allocate a new uninitialized place")
    }
}

macro_rules! place_construct {
    (@TARGET) => [Self::Target];
    (@TARGET $target:ty) => [$target];

    {$(
        $(#[$ty_meta:meta])*
        $v:vis trait $ty:ident $([$($g:tt)*] $(where [$($w:tt)*])?)? = {
            $(args: { $($arg_name:ident: $arg_ty:ty),* $(,)? },)?
            $(items: { $($(#[$item_meta:meta])* $item_name:ident: [$($item_bounds:tt)*]),* $(,)? },)?
            $(target: $target:ty as $target_g:ty,)?
            funcs: [
                $(#[$try_new_meta:meta])*
                $try_new:ident,
                $(#[$new_meta:meta])*
                $new:ident,
                $(#[$try_pin_meta:meta])*
                $try_pin:ident,
                $(#[$pin_meta:meta])*
                $pin:ident $(,)?
            ]
        };
    )*} => {$(
        $(#[$ty_meta])*
        #[allow(unused_parens, clippy::double_parens)]
        $v trait $ty$(<$($g)*>)?: PlaceConstruct<($($($arg_ty),*)?) $(, Target = $target)?>
            $($(where $($w)*)?)?
        {
            $($(
                $(#[$item_meta])*
                type $item_name: $($item_bounds)*;
            )*)?

            $(#[$try_new_meta])*
            fn $try_new<M, I>($($($arg_name: $arg_ty,)*)? init: I) -> Result<Self, I::Error>
            where
                I: IntoInit<
                    place_construct![@TARGET $($target)?],
                    M,
                >,
                I::Error: From<Self::Error>,
            {
                let place = Self::try_new_uninit_in(($($($arg_name),*)?))?;
                place.try_init(init).map_err(|(e, _)| e)
            }

            $(#[$new_meta])*
            fn $new<M, I>($($($arg_name: $arg_ty,)*)? init: I) -> Self
            where
                I: IntoInit<
                    place_construct![@TARGET $($target)?],
                    M,
                >,
            {
                Self::new_uninit_in(($($($arg_name),*)?)).init(init)
            }

            $(#[$try_pin_meta])*
            fn $try_pin<M, I>($($($arg_name: $arg_ty,)*)? init: I) -> Result<Pin<Self>, I::Error>
            where
                Self: Deref,
                I: IntoInitPin<place_construct![@TARGET $($target)?], M>,
                I::Error: From<Self::Error>,
            {
                let place = Self::try_new_uninit_in(($($($arg_name),*)?))?;
                place.try_init_pin(init).map_err(|(e, _)| e)
            }

            $(#[$pin_meta])*
            fn $pin<M, I>($($($arg_name: $arg_ty,)*)? init: I) -> Pin<Self>
            where
                Self: Deref,
                I: IntoInitPin<place_construct![@TARGET $($target)?], M>,
            {
                Self::new_uninit_in(($($($arg_name),*)?)).init_pin(init)
            }
        }

        #[allow(unused_parens, clippy::double_parens)]
        impl<
            $($($item_name: $($item_bounds)*,)*)?
            P: PlaceConstruct<($($($arg_ty),*)?) $(, Target = $target_g)?>,
            $($($($w)*)?)?
        > $ty $(<$($g)*>)? for P {
            $($(
                type $item_name = $item_name;
            )*)?
        }
    )*};
}

place_construct! {
    /// A place that can be constructed by default methods.
    pub trait PlaceNew = {
        funcs: [
            /// Tries to create a new place by initializing it with the
            /// given initializer.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let init = init::with(|| 42).adapt_err::<AllocError>();
            /// let b = Box::try_new_with(init).unwrap();
            /// assert_eq!(*b, 42);
            /// ```
            try_new_with,
            /// Creates a new place by initializing it with the given
            /// initializer.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use placid::prelude::*;
            /// let b = Box::new_with(init::with(|| 42));
            /// assert_eq!(*b, 42);
            /// ```
            new_with,
            /// Tries to create a new pinned place by initializing it with
            /// the given initializer.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let init = init::with(|| 42).adapt_err::<AllocError>();
            /// let b = Box::try_pin_with(init).unwrap();
            /// assert_eq!(*b, 42);
            /// ```
            try_pin_with,
            /// Creates a new pinned place by initializing it with the given
            /// initializer.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use placid::prelude::*;
            /// let b = Box::pin_with(init::with(|| 42));
            /// assert_eq!(*b, 42);
            /// ```
            pin_with,
        ]
    };

    /// A place that can be constructed with a specified argument.
    pub trait PlaceNewIn[A] where [A:] = {
        args: { arg: A },
        funcs: [
            /// Tries to create a new place by initializing it with the
            /// given initializer and argument.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::{AllocError, Global};
            ///
            /// let init = init::with(|| 42).adapt_err::<AllocError>();
            /// let b = Box::try_new_within(Global, init).unwrap();
            /// assert_eq!(*b, 42);
            /// ```
            try_new_within,
            /// Creates a new place by initializing it with the given
            /// initializer and argument.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::Global;
            ///
            /// let b = Box::new_within(Global, init::with(|| 42));
            /// assert_eq!(*b, 42);
            /// ```
            new_within,
            /// Tries to create a new pinned place by initializing it with the
            /// given initializer and argument.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::{AllocError, Global};
            ///
            /// let init = init::with(|| 42).adapt_err::<AllocError>();
            /// let b = Box::try_pin_within(Global, init).unwrap();
            /// assert_eq!(*b, 42);
            /// ```
            try_pin_within,
            /// Creates a new pinned place by initializing it with the given
            /// initializer and argument.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::Global;
            ///
            /// let b = Box::pin_within(Global, init::with(|| 42));
            /// assert_eq!(*b, 42);
            /// ```
            pin_within,
        ]
    };

    /// A place that can be constructed as a slice with a specified length.
    pub trait PlaceSlice = {
        args: { len: usize },
        items: {
            /// The element type of the slice.
            Item: [],
        },
        target: [Self::Item] as [Item],
        funcs: [
            /// Tries to create a new slice place by initializing it with the
            /// given initializer.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let init = init::repeat(42).adapt_err::<AllocError>();
            /// let slice = Box::try_new_slice(3, init).unwrap();
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            try_new_slice,
            /// Creates a new slice place by initializing it with the given
            /// initializer.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use placid::prelude::*;
            /// let slice = Box::new_slice(3, init::repeat(42));
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            new_slice,
            /// Tries to create a new pinned slice place by initializing it with
            /// the given initializer.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let init = init::repeat(42).adapt_err::<AllocError>();
            /// let slice = Box::try_pin_slice(3, init).unwrap();
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            try_pin_slice,
            /// Creates a new pinned slice place by initializing it with the
            /// given initializer.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use placid::prelude::*;
            /// let slice = Box::pin_slice(3, init::repeat(42));
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            pin_slice,
        ]
    };

    /// A place that can be constructed as a slice with a specified length
    /// and allocator.
    pub trait PlaceSliceIn[A] where [A: Allocator] = {
        args: { len: usize, alloc: A },
        items: {
            /// The element type of the slice.
            Item: [],
        },
        target: [Self::Item] as [Item],
        funcs: [
            /// Tries to create a new slice place by initializing it with the
            /// given initializer and allocator.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let a = std::alloc::Global;
            /// let init = init::repeat(42).adapt_err::<AllocError>();
            /// let slice = Box::try_new_slice_in(3, a, init).unwrap();
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            try_new_slice_in,
            /// Creates a new slice place by initializing it with the given
            /// initializer and allocator.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            ///
            /// let a = std::alloc::Global;
            /// let slice = Box::new_slice_in(3, a, init::repeat(42));
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            new_slice_in,
            /// Tries to create a new pinned slice place by initializing it with
            /// the given initializer and allocator.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let a = std::alloc::Global;
            /// let init = init::repeat(42).adapt_err::<AllocError>();
            /// let slice = Box::try_pin_slice_in(3, a, init).unwrap();
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            try_pin_slice_in,
            /// Creates a new pinned slice place by initializing it with the
            /// given initializer and allocator.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            ///
            /// let a = std::alloc::Global;
            /// let slice = Box::pin_slice_in(3, a, init::repeat(42));
            /// assert_eq!(&*slice, &[42, 42, 42]);
            /// ```
            pin_slice_in,
        ]
    };

    /// A place that can be constructed as a string with a specified length.
    pub trait PlaceStr = {
        args: { len: usize },
        target: str as str,
        funcs: [
            /// Tries to create a new string place by initializing it with the
            /// given initializer.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let init = init::str("hello").map_err(|_| AllocError);
            /// let s = Box::try_new_str(5, init).unwrap();
            /// assert_eq!(&*s, "hello");
            /// ```
            try_new_str,
            /// Creates a new string place by initializing it with the given
            /// initializer.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use placid::prelude::*;
            /// let s = Box::new_str(5, "hello");
            /// assert_eq!(&*s, "hello");
            /// ```
            new_str,
            /// Tries to create a new pinned string place by initializing it with
            /// the given initializer.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let init = init::str("hello").map_err(|_| AllocError);
            /// let s = Box::try_pin_str(5, init).unwrap();
            /// assert_eq!(&*s, "hello");
            /// ```
            try_pin_str,
            /// Creates a new pinned string place by initializing it with the
            /// given initializer.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// use placid::prelude::*;
            /// let s = Box::pin_str(5, "hello");
            /// assert_eq!(&*s, "hello");
            /// ```
            pin_str,
        ]
    };

    /// A place that can be constructed as a string with a specified length
    /// and allocator.
    pub trait PlaceStrIn[A] where [A: Allocator] = {
        args: { len: usize, alloc: A },
        target: str as str,
        funcs: [
            /// Tries to create a new string place by initializing it with the
            /// given initializer and allocator.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let a = std::alloc::Global;
            /// let init = init::str("hello").map_err(|_| AllocError);
            /// let s = Box::try_new_str_in(5, a, init).unwrap();
            /// assert_eq!(&*s, "hello");
            /// ```
            try_new_str_in,
            /// Creates a new string place by initializing it with the given
            /// initializer and allocator.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            ///
            /// let a = std::alloc::Global;
            /// let s = Box::new_str_in(5, a, "hello");
            /// assert_eq!(&*s, "hello");
            /// ```
            new_str_in,
            /// Tries to create a new pinned string place by initializing it with
            /// the given initializer and allocator.
            ///
            /// # Errors
            ///
            /// If place creation or the initialization fails, this method
            /// returns an error.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            /// use std::alloc::AllocError;
            ///
            /// let a = std::alloc::Global;
            /// let init = init::str("hello").map_err(|_| AllocError);
            /// let s = Box::try_pin_str_in(5, a, init).unwrap();
            /// assert_eq!(&*s, "hello");
            /// ```
            try_pin_str_in,
            /// Creates a new pinned string place by initializing it with the
            /// given initializer and allocator.
            ///
            /// # Panics
            ///
            /// This method will panic if place creation or the initialization
            /// fails.
            ///
            /// # Examples
            ///
            /// ```rust
            /// #![feature(allocator_api)]
            /// use placid::prelude::*;
            ///
            /// let a = std::alloc::Global;
            /// let s = Box::pin_str_in(5, a, "hello");
            /// assert_eq!(&*s, "hello");
            /// ```
            pin_str_in,
        ]
    };
}
