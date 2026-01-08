use core::{fmt, pin::Pin};

use crate::{
    Own, Uninit,
    pin::{DropSlot, POwn},
};

/// An error that occurs during initialization of a place.
#[derive(thiserror::Error)]
#[error("failed to initialize place: {error}")]
pub struct Error<'a, T: ?Sized, E> {
    /// The error that occurred during initialization.
    #[source]
    pub error: E,
    /// The place that failed to be initialized.
    pub place: Uninit<'a, T>,
}

impl<'a, T: ?Sized, E: fmt::Debug> fmt::Debug for Error<'a, T, E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Error")
            .field("error", &self.error)
            .field("place", &self.place)
            .finish()
    }
}

/// A trait for initializing a place with a pinned value.
///
/// This trait is used to abstract over the different ways a place can be
/// initialized. See the implementors for more details.
pub trait InitPin<T: ?Sized, Marker = ()>: Sized {
    type Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>>;

    fn inspect<F: FnOnce(Pin<&mut T>)>(self, f: F) -> Inspect<Self, F> {
        inspect_pin(self, f)
    }
}

/// A trait for initializing a place with a value.
///
/// This trait is used to abstract over the different ways a place can be
/// initialized. See the implementors for more details.
pub trait Init<T: ?Sized, Marker = ()>: InitPin<T, Marker> {
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>>;

    fn inspect<F: FnOnce(&mut T)>(self, f: F) -> Inspect<Self, F> {
        inspect(self, f)
    }
}

mod inspect;
pub use self::inspect::{Inspect, inspect, inspect_pin};

mod raw;
pub use self::raw::{raw, raw_pin, try_raw, try_raw_pin};

mod slice;
pub use self::slice::{SliceError, repeat, repeat_with, slice};

mod value;
pub use self::value::{of, try_with, with};
