use core::{fmt, pin::Pin};

use crate::{
    Own, Uninit,
    pin::{DropSlot, POwn},
};

/// An error that occurs during initialization of a place.
#[derive(thiserror::Error)]
#[error("failed to initialize in pinned place: {error}")]
pub struct InitPinError<'a, 'b, T: ?Sized, E> {
    /// The error that occurred during initialization.
    #[source]
    pub error: E,
    /// The place that failed to be initialized.
    pub place: Uninit<'a, T>,
    /// The drop slot associated with the initialized place.
    pub slot: DropSlot<'a, 'b, T>,
}

impl<'a, 'b, T: ?Sized, E> InitPinError<'a, 'b, T, E> {
    pub fn from_init(err: InitError<'a, T, E>, slot: DropSlot<'a, 'b, T>) -> Self {
        InitPinError {
            error: err.error,
            place: err.place,
            slot,
        }
    }
}

impl<'a, 'b, T: ?Sized, E: fmt::Debug> fmt::Debug for InitPinError<'a, 'b, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error")
            .field("error", &self.error)
            .field("place", &self.place)
            .field("slot", &self.slot)
            .finish()
    }
}

pub type InitPinResult<'a, 'b, I> = Result<
    POwn<'b, <I as InitPin>::Target>,
    InitPinError<'a, 'b, <I as InitPin>::Target, <I as InitPin>::Error>,
>;

/// A trait for initializing a place with a pinned value.
///
/// This trait is used to abstract over the different ways a place can be
/// initialized. See the implementors for more details.
pub trait InitPin: Sized {
    type Target: ?Sized;
    type Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, Self::Target>,
        slot: DropSlot<'a, 'b, Self::Target>,
    ) -> InitPinResult<'a, 'b, Self>;

    fn and<F: FnOnce(Pin<&mut Self::Target>)>(self, f: F) -> AndPin<Self, F> {
        and_pin(self, f)
    }

    fn or<M, I2>(self, other: I2) -> Or<Self, I2, M>
    where
        I2: IntoInit<Self::Target, M, Error = Self::Error>,
    {
        or(self, other)
    }

    fn or_else<F, I2>(self, f: F) -> OrElse<Self, F>
    where
        F: FnOnce(Self::Error) -> I2,
        I2: InitPin<Target = Self::Target, Error = Self::Error>,
    {
        or_else(self, f)
    }
}

/// An error that occurs during initialization of a place.
#[derive(thiserror::Error)]
#[error("failed to initialize in place: {error}")]
pub struct InitError<'a, T: ?Sized, E> {
    /// The error that occurred during initialization.
    #[source]
    pub error: E,
    /// The place that failed to be initialized.
    pub place: Uninit<'a, T>,
}

impl<'a, T: ?Sized, E> InitError<'a, T, E> {
    pub fn into_pin<'b>(self, slot: DropSlot<'a, 'b, T>) -> InitPinError<'a, 'b, T, E> {
        InitPinError {
            error: self.error,
            place: self.place,
            slot,
        }
    }
}

impl<'a, 'b, T: ?Sized, E> From<InitPinError<'a, 'b, T, E>> for InitError<'a, T, E> {
    fn from(err: InitPinError<'a, 'b, T, E>) -> Self {
        InitError {
            error: err.error,
            place: err.place,
        }
    }
}

impl<'a, T: ?Sized, E: fmt::Debug> fmt::Debug for InitError<'a, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error")
            .field("error", &self.error)
            .field("place", &self.place)
            .finish()
    }
}

pub type InitResult<'a, I> = Result<
    Own<'a, <I as InitPin>::Target>,
    InitError<'a, <I as InitPin>::Target, <I as InitPin>::Error>,
>;

/// A trait for initializing a place with a value.
///
/// This trait is used to abstract over the different ways a place can be
/// initialized. See the implementors for more details.
pub trait Init: InitPin {
    fn init(self, place: Uninit<'_, Self::Target>) -> InitResult<'_, Self>;

    fn and<F: FnOnce(&mut Self::Target)>(self, f: F) -> And<Self, F> {
        and(self, f)
    }
}

/// A trait for converting a value into an initializer.
///
/// This trait is used to allow types to be directly used as initializers
/// without needing to wrap them in a specific initializer factory function.
pub trait IntoInit<T: ?Sized, Marker = ()>: Sized {
    type Init: InitPin<Target = T, Error = Self::Error>;
    type Error;

    fn into_init(self) -> Self::Init;
}

impl<I: InitPin> IntoInit<I::Target> for I {
    type Init = I;
    type Error = I::Error;

    fn into_init(self) -> Self::Init {
        self
    }
}

mod and;
pub use self::and::{And, AndPin, and, and_pin};

mod or;
pub use self::or::{Or, OrElse, or, or_else};

mod raw;
pub use self::raw::{Raw, RawPin, TryRaw, TryRawPin, raw, raw_pin, try_raw, try_raw_pin};

mod slice;
pub use self::slice::{Repeat, RepeatWith, Slice, SliceError, repeat, repeat_with, slice};

mod value;
pub use self::value::{TryWith, Value, With, try_with, value, with};
