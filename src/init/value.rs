use core::convert::Infallible;

use crate::{
    init::{
        Init, InitError, InitPin, InitPinError, InitPinResult, InitResult, Initializer, IntoInit,
    },
    pin::DropSlot,
    uninit::Uninit,
};

/// Initializes a place with a directly-provided value.
///
/// This initializer is created by the [`value()`] factory function.
#[derive(Debug, PartialEq)]
pub struct Value<T>(T);

impl<T> Initializer for Value<T> {
    type Error = Infallible;
}

impl<T> InitPin<T> for Value<T> {
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, Infallible> {
        (*place).write(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T> Init<T> for Value<T> {
    #[inline]
    fn init(self, mut place: Uninit<'_, T>) -> InitResult<'_, T, Infallible> {
        (*place).write(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

/// Creates an initializer for a directly-provided value.
///
/// This is a convenience factory function for creating a [`Value`] initializer.
/// The value is moved into the place and cannot fail.
///
/// This is typically not needed directly, as all types that implement `Clone`
/// automatically implement `IntoInit` for `Value<T>`, allowing their objects to
/// be used directly as initializers.
///
/// ```rust
/// use placid::prelude::*;
///
/// let owned = own!(42);
/// assert_eq!(*owned, 42);
/// ```
///
/// Instead, use the `value()` function directly to combine with other
/// initializers:
///
/// ```rust
/// use placid::prelude::*;
///
/// let uninit: Uninit<i32> = uninit!();
/// let owned = uninit.write(init::value(100).and(|v| *v += 23));
/// assert_eq!(*owned, 123);
/// ```
///
/// [`Value`]: crate::init::Value
/// [`own!`]: macro@crate::own
#[inline]
pub const fn value<T>(value: T) -> Value<T> {
    Value(value)
}

impl<T: Clone> IntoInit<T, Value<T>> for T {
    type Init = Value<T>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        Value(self)
    }
}

/// Initializes a place by calling a closure that returns a Result.
///
/// This initializer is created by the [`try_with()`] factory function.
#[derive(Debug, PartialEq)]
pub struct TryWith<F>(F);

impl<T, E, F> Initializer for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    type Error = E;
}

impl<T, E, F> InitPin<T> for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, E> {
        match (self.0)() {
            Ok(value) => {
                (*place).write(value);
                // SAFETY: The place is now initialized.
                Ok(unsafe { place.assume_init_pin(slot) })
            }
            Err(e) => Err(InitPinError { error: e, place, slot }),
        }
    }
}

impl<T, F, E> Init<T> for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    #[inline]
    fn init(self, mut place: Uninit<'_, T>) -> InitResult<'_, T, E> {
        match (self.0)() {
            Ok(value) => {
                (*place).write(value);
                // SAFETY: The place is now initialized.
                Ok(unsafe { place.assume_init() })
            }
            Err(e) => Err(InitError { error: e, place }),
        }
    }
}

/// Initializes a place by calling a closure that returns a Result.
///
/// This is similar to [`with`], but the closure returns a [`Result`],
/// allowing for fallible initialization. If the closure returns an error, the
/// initialization fails and the error is returned to the caller.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let uninit: Uninit<u32> = uninit!();
/// let result = uninit.try_write(init::try_with(|| {
///     // Some computation that might fail
///     if true {
///         Ok(42u32)
///     } else {
///         Err("computation failed")
///     }
/// }));
/// assert!(result.is_ok());
/// assert_eq!(*result.unwrap(), 42);
///
/// // With a failing computation
/// let uninit: Uninit<u32> = uninit!();
/// let result = uninit.try_write(init::try_with(|| {
///     Err::<u32, &str>("failed")
/// }));
/// assert!(result.is_err());
/// ```
///
/// [`with`]: crate::init::with
#[inline]
pub const fn try_with<T, F, E>(f: F) -> TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    TryWith(f)
}

impl<T, E, F> IntoInit<T, TryWith<F>> for F
where
    F: FnOnce() -> Result<T, E>,
{
    type Init = TryWith<F>;
    type Error = E;

    #[inline]
    fn into_init(self) -> Self::Init {
        TryWith(self)
    }
}

/// Initializes a place by calling a closure that returns a value.
///
/// This initializer is created by the [`with()`] factory function.
#[derive(Debug, PartialEq)]
pub struct With<F>(F);

impl<F> Initializer for With<F> {
    type Error = Infallible;
}

impl<T, F> InitPin<T> for With<F>
where
    F: FnOnce() -> T,
{
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, Infallible> {
        (*place).write((self.0)());
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T, F> Init<T> for With<F>
where
    F: FnOnce() -> T,
{
    #[inline]
    fn init(self, mut place: Uninit<'_, T>) -> InitResult<'_, T, Infallible> {
        (*place).write((self.0)());
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

/// Creates an initializer from a closure that produces a value.
///
/// For a fallible counterpart, see [`try_with()`].
///
/// # Examples
///
/// Using the `with()` function:
/// ```rust
/// use placid::prelude::*;
///
/// let uninit = uninit!(String);
/// let owned = uninit.write(init::with(|| String::from("Lazy initialization")));
/// assert_eq!(&*owned, "Lazy initialization");
/// ```
///
/// Using with [`own!`] macro directly:
///
/// ```rust
/// use placid::prelude::*;
///
/// let owned: Own<String> = own!(|| String::from("hello"));
/// assert_eq!(&*owned, "hello");
/// ```
///
/// [`own!`]: macro@crate::own
#[inline]
pub const fn with<T, F>(f: F) -> With<F>
where
    F: FnOnce() -> T,
{
    With(f)
}

impl<T, F> IntoInit<T, With<F>> for F
where
    F: FnOnce() -> T,
{
    type Init = With<F>;
    type Error = Infallible;

    #[inline]
    fn into_init(self) -> Self::Init {
        With(self)
    }
}
