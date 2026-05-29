use core::{
    clone::CloneToUninit,
    convert::Infallible,
    mem::{self, size_of_val_raw},
    ptr,
};

use crate::{
    init::{
        Init, InitError, InitPin, InitPinError, InitPinResult, InitResult, Initializer, IntoInitPin,
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
/// can be used directly as initializers.
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

impl<T: Clone> IntoInitPin<T, Value<T>> for T {
    type Init = Value<T>;
    type Error = Infallible;

    #[inline]
    fn into_init(self) -> Self::Init {
        Value(self)
    }
}

/// Initializes a place by calling a closure that returns a Result.
///
/// This initializer is created by the [`try_with()`] factory function.
#[derive(Debug, PartialEq)]
pub struct TryWith<F>(F);

impl<T, E: core::fmt::Debug, F> Initializer for TryWith<F>
where
    F: FnOnce() -> Result<T, E>,
{
    type Error = E;
}

impl<T, E: core::fmt::Debug, F> InitPin<T> for TryWith<F>
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

impl<T, F, E: core::fmt::Debug> Init<T> for TryWith<F>
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

impl<T, E: core::fmt::Debug, F> IntoInitPin<T, TryWith<F>> for F
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

impl<T, F> IntoInitPin<T, With<F>> for F
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

/// The error type for the moving and cloning initializer when the size of the
/// source value does not match the size of the destination place.
#[derive(Debug, thiserror::Error)]
#[error("object size mismatch")]
pub struct ValueError;

/// Creates an initializer that clones a value from a reference.
///
/// This initializer is created by the [`clone()`] factory function.
#[derive(Debug, PartialEq)]
pub struct CloneInit<'a, T: ?Sized>(&'a T);

impl<T: ?Sized> Initializer for CloneInit<'_, T> {
    type Error = ValueError;
}

impl<T: ?Sized + CloneToUninit> InitPin<T> for CloneInit<'_, T> {
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, ValueError> {
        let src = self.0;
        let dst = place.as_mut_ptr();

        let size = size_of_val(src);
        // SAFETY: The pointer metadata of `dst` is always valid since `Uninit<T>`
        // points to a valid uninitialized memory for `T`.
        if size != unsafe { size_of_val_raw(dst) } {
            return Err(InitPinError::new(ValueError, place, slot));
        }

        // SAFETY: `src` and `dst` are valid for reads/writes of `size` bytes.
        unsafe { src.clone_to_uninit(dst.cast()) };

        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T: ?Sized + CloneToUninit> Init<T> for CloneInit<'_, T> {
    #[inline]
    fn init(self, mut place: Uninit<'_, T>) -> InitResult<'_, T, ValueError> {
        let src = self.0;
        let dst = place.as_mut_ptr();

        let size = size_of_val(src);
        // SAFETY: The pointer metadata of `dst` is always valid since `Uninit<T>`
        // points to a valid uninitialized memory for `T`.
        if size != unsafe { size_of_val_raw(dst) } {
            return Err(InitError::new(ValueError, place));
        }

        // SAFETY: `src` and `dst` are valid for reads/writes of `size` bytes.
        unsafe { src.clone_to_uninit(dst.cast()) };

        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

/// Creates an initializer that clones a value from a reference.
///
/// The provided value is not necessarily [`Sized`], but the initializer will
/// fail if the size of the value does not match the size of the destination
/// place, which could only happen if unsized.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let src = String::from("hello");
/// let uninit: Uninit<String> = uninit!(String);
/// let result = uninit.write(init::clone(&src));
/// assert_eq!(*result, String::from("hello"));
/// ```
#[inline]
pub const fn clone<T: ?Sized + CloneToUninit>(this: &T) -> CloneInit<'_, T> {
    CloneInit(this)
}

impl<'a, T: ?Sized + CloneToUninit> IntoInitPin<T, CloneInit<'a, T>> for &'a T {
    type Init = CloneInit<'a, T>;
    type Error = ValueError;

    #[inline]
    fn into_init(self) -> Self::Init {
        CloneInit(self)
    }
}
