//! Defines traits and implementations for constructing places in memory
//! with specified arguments.

use core::{alloc::Allocator, fmt, ops::Deref, pin::Pin};

use crate::{
    init::{Init, IntoInit},
    place::Place,
};

/// A place in memory that can be created with specified arguments.
pub trait PlaceConstruct<Args>: Sized + Deref {
    /// The uninitialized place type that can be constructed into `Self`.
    type Uninit: Place<Self::Target, Init = Self>;
    /// The error type that can occur during construction.
    type Error;

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
    fn new_uninit_in(args: Args) -> Self::Uninit
    where
        Self::Error: fmt::Debug,
    {
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
                    Init: Init<place_construct![@TARGET $($target)?]>
                >,
                I::Error: From<Self::Error>,
            {
                let place = Self::try_new_uninit_in(($($($arg_name),*)?))?;
                place.try_init(init).map_err(|(e, _)| e)
            }

            $(#[$new_meta])*
            fn $new<M, I>($($($arg_name: $arg_ty,)*)? init: I) -> Self
            where
                Self::Error: fmt::Debug,
                I: IntoInit<
                    place_construct![@TARGET $($target)?],
                    M,
                    Init: Init<place_construct![@TARGET $($target)?]>,
                    Error: fmt::Debug
                >,
            {
                Self::new_uninit_in(($($($arg_name),*)?)).init(init)
            }

            $(#[$try_pin_meta])*
            fn $try_pin<M, I>($($($arg_name: $arg_ty,)*)? init: I) -> Result<Pin<Self>, I::Error>
            where
                Self: Deref,
                I: IntoInit<place_construct![@TARGET $($target)?], M>,
                I::Error: From<Self::Error>,
            {
                let place = Self::try_new_uninit_in(($($($arg_name),*)?))?;
                place.try_init_pin(init).map_err(|(e, _)| e)
            }

            $(#[$pin_meta])*
            fn $pin<M, I>($($($arg_name: $arg_ty,)*)? init: I) -> Pin<Self>
            where
                Self: Deref,
                Self::Error: fmt::Debug,
                I: IntoInit<place_construct![@TARGET $($target)?], M, Error: fmt::Debug>,
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
            /// Creates a new place by initializing it with the given initializer.
            try_new_with,
            /// Creates a new place by initializing it with the given initializer.
            new_with,
            /// Creates a new pinned place by initializing it with the given
            /// initializer.
            try_pin_with,
            /// Creates a new pinned place by initializing it with the given
            /// initializer.
            pin_with,
        ]
    };

    /// A place that can be constructed with a specified allocator.
    pub trait PlaceNewIn[A] where [A: Allocator] = {
        args: { alloc: A },
        funcs: [
            /// Creates a new place by initializing it with the given initializer.
            try_new_within,
            /// Creates a new place by initializing it with the given initializer.
            new_within,
            /// Creates a new pinned place by initializing it with the given
            /// initializer.
            try_pin_within,
            /// Creates a new pinned place by initializing it with the given
            /// initializer.
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
            /// Creates a new slice place by initializing it with the given initializer.
            try_new_slice,
            /// Creates a new slice place by initializing it with the given initializer.
            new_slice,
            /// Creates a new pinned slice place by initializing it with the given
            /// initializer.
            try_pin_slice,
            /// Creates a new pinned slice place by initializing it with the given
            /// initializer.
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
            /// Creates a new slice place by initializing it with the given initializer.
            try_new_slice_in,
            /// Creates a new slice place by initializing it with the given initializer.
            new_slice_in,
            /// Creates a new pinned slice place by initializing it with the given
            /// initializer.
            try_pin_slice_in,
            /// Creates a new pinned slice place by initializing it with the given
            /// initializer.
            pin_slice_in,
        ]
    };

    /// A place that can be constructed as a string with a specified length.
    pub trait PlaceStr = {
        args: { len: usize },
        target: str as str,
        funcs: [
            /// Creates a new string place by initializing it with the given initializer.
            try_new_str,
            /// Creates a new string place by initializing it with the given initializer.
            new_str,
            /// Creates a new pinned string place by initializing it with the given
            /// initializer.
            try_pin_str,
            /// Creates a new pinned string place by initializing it with the given
            /// initializer.
            pin_str,
        ]
    };

    /// A place that can be constructed as a string with a specified length
    /// and allocator.
    pub trait PlaceStrIn[A] where [A: Allocator] = {
        args: { len: usize, alloc: A },
        target: str as str,
        funcs: [
            /// Creates a new string place by initializing it with the given initializer.
            try_new_str_in,
            /// Creates a new string place by initializing it with the given initializer.
            new_str_in,
            /// Creates a new pinned string place by initializing it with the given
            /// initializer.
            try_pin_str_in,
            /// Creates a new pinned string place by initializing it with the given
            /// initializer.
            pin_str_in,
        ]
    };
}
