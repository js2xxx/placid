use core::convert::Infallible;

use crate::{
    Uninit,
    init::{Init, InitError, InitPin, InitPinError, InitPinResult, InitResult, IntoInit},
    pin::DropSlot,
};

/// Initializes a place with a directly-provided value.
///
/// This initializer is created by the [`value()`] factory function.
pub struct Value<T>(T);

impl<T> InitPin for Value<T> {
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        (*place).write(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T> Init for Value<T> {
    fn init(self, mut place: Uninit<'_, T>) -> InitResult<'_, Self> {
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
/// This is typically not needed directly, as the [`own!`] macro provides a
/// more ergonomic interface:
///
/// ```rust
/// use placid::own;
///
/// let owned = own!(42);
/// assert_eq!(*owned, 42);
/// ```
///
/// Instead, use the `value()` function directly to combine with other
/// initializers:
///
/// ```rust
/// use placid::{uninit, Uninit, init::{value, Init}};
///
/// let uninit: Uninit<i32> = uninit!();
/// let owned = uninit.write(value(100).and(|v| *v += 23));
/// assert_eq!(*owned, 123);
/// ```
///
/// [`Value`]: crate::init::Value
/// [`own!`]: macro@crate::own
pub const fn value<T>(value: T) -> Value<T> {
    Value(value)
}

impl<T> IntoInit<T, Value<T>> for T {
    type Init = Value<T>;
    type Error = Infallible;

    fn into_init(self) -> Self::Init {
        Value(self)
    }
}

/// Initializes a place by calling a closure that returns a Result.
///
/// This initializer is created by the [`try_with()`] factory function.
pub struct TryWith<F>(F);

impl<T, E, F> InitPin for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    type Target = T;
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        match (self.0)() {
            Ok(value) => Ok(place.write_pin(value, slot)),
            Err(e) => Err(InitPinError { error: e, place, slot }),
        }
    }
}

impl<T, F, E> Init for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, Self> {
        match (self.0)() {
            Ok(value) => Ok(place.write(value)),
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
/// use placid::{uninit, Uninit, init::try_with};
///
/// let uninit: Uninit<u32> = uninit!();
/// let result = uninit.try_write(try_with(|| {
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
/// let result = uninit.try_write(try_with(|| {
///     Err::<u32, &str>("failed")
/// }));
/// assert!(result.is_err());
/// ```
///
/// [`with`]: crate::init::with
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

    fn into_init(self) -> Self::Init {
        TryWith(self)
    }
}

/// Initializes a place by calling a closure that returns a value.
///
/// This initializer is created by the [`with()`] factory function.
pub struct With<F>(F);

impl<T, F> InitPin for With<F>
where
    F: FnOnce() -> T,
{
    type Target = T;
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, Self> {
        place.try_write_pin::<_, Value<T>>((self.0)(), slot)
    }
}

impl<T, F> Init for With<F>
where
    F: FnOnce() -> T,
{
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, Self> {
        place.try_write((self.0)())
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
/// use placid::{uninit, init::with};
///
/// let uninit = uninit!(String);
/// let owned = uninit.write(with(|| String::from("Lazy initialization")));
/// assert_eq!(&*owned, "Lazy initialization");
/// ```
///
/// Using with [`own!`] macro directly:
///
/// ```rust
/// use placid::{own, Own};
///
/// let owned: Own<String> = own!(|| String::from("hello"));
/// assert_eq!(&*owned, "hello");
/// ```
///
/// [`own!`]: macro@crate::own
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

    fn into_init(self) -> Self::Init {
        With(self)
    }
}
