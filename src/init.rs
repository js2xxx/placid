//! Traits and types for initializing places.
//!
//! This module defines the [`Init`] and [`InitPin`] traits, which provide
//! abstractions for initializing uninitialized memory places. It also includes
//! various initializers and combinators for building complex initialization
//! patterns.

use core::{convert::Infallible, fmt, pin::Pin};

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
    /// Creates a new `InitPinError`.
    pub const fn new(error: E, place: Uninit<'a, T>, slot: DropSlot<'a, 'b, T>) -> Self {
        InitPinError { error, place, slot }
    }

    /// Maps the error contained in this `InitPinError` to a different error
    /// type.
    pub fn map<F, E2>(self, f: F) -> InitPinError<'a, 'b, T, E2>
    where
        F: FnOnce(E) -> E2,
    {
        InitPinError {
            error: f(self.error),
            place: self.place,
            slot: self.slot,
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

/// The result type for [pinned initialization].
///
/// [pinned initialization]: crate::init::InitPin::init_pin
pub type InitPinResult<'a, 'b, T, E> = Result<POwn<'b, T>, InitPinError<'a, 'b, T, E>>;

/// A trait for initializing a place with a pinned value.
///
/// This trait is used to abstract over the different ways a place can be
/// initialized. See the implementors for more details.
///
/// # Safety
///
/// This trait is itself safe to implement. However, care must be taken when
/// implementing the `init_pin` method to ensure the pinning guarantees if
/// hand-written unsafe code is involved.
///
/// An important aspect worth noting is that the `init_pin` method **cannot
/// leave a partially-pin-initialized state** in the provided `place` even if
/// initialization fails. This is crucial to maintain the safety guarantees of
/// the pinning abstraction.
///
/// For example, when pin-initializing a struct:
///
/// ```ignore
/// #[pin]
/// struct A {
///     #[pin]
///     b: B,
///     c: C,
/// }
/// ```
///
/// If the initialization of field `b` succeeds before the initialization of
/// field `c` fails, **`b` must be dropped before returning the error or
/// resuming the panic**. On the other hand, if the initialization of `b` fails
/// after `c` is initialized, no cleanup is necessary since `c` is not pinned
/// and can be safely `mem::forget`ed.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not a pin-initializer for places of type `{T}`",
    label = "`{Self}` is not a pin-initializer for type `{T}`"
)]
pub trait InitPin<T: ?Sized>: Sized {
    /// The error type that can occur during initialization.
    type Error;

    /// Initializes a place with a pinned value.
    ///
    /// This method performs the actual initialization of an uninitialized
    /// place, creating a pinned reference to the initialized value. It
    /// requires both an uninitialized place and a drop slot to manage the
    /// value's lifetime.
    ///
    /// # Arguments
    ///
    /// * `place` - The uninitialized place to initialize
    /// * `slot` - The drop slot for managing the pinned value's lifetime
    ///
    /// # Returns
    ///
    /// Returns a [pinned owned reference] on success, or an [`InitPinError`]
    /// containing the error and the failed place.
    ///
    /// [pinned owned reference]: crate::pin::POwn
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> InitPinResult<'a, 'b, T, Self::Error>;

    /// Chains a closure to execute after successful initialization with a
    /// pinned reference.
    ///
    /// This method allows you to perform additional setup on the initialized
    /// value while maintaining its pinned status. The closure receives a
    /// mutable pinned reference to the newly initialized value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{pown, POwn, init::*};
    /// use core::pin::Pin;
    ///
    /// let owned: POwn<Vec<_>> = pown!(
    ///     value(vec![1, 2, 3]).and_pin(|mut v| v.as_mut().push(4))
    /// );
    /// assert_eq!(*owned, [1, 2, 3, 4]);
    /// ```
    fn and_pin<F: FnOnce(Pin<&mut T>)>(self, f: F) -> AndPin<Self, F> {
        and_pin(self, f)
    }

    /// Provides a fallback initializer if this one fails.
    ///
    /// If initialization fails, the `other` initializer will be attempted
    /// instead. The `other` initializer must produce the same target type
    /// and have an error that can be converted to this initializer's error
    /// type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{own, Own, init::*};
    ///
    /// let owned: Own<u32> = own!(value(10u32).or(20u32));
    /// assert_eq!(*owned, 10);
    ///
    /// let failed: Own<u32> = own!(try_with(|| u32::try_from(-1i32)).or(30u32));
    /// assert_eq!(*failed, 30);
    /// ```
    fn or<M, I2>(self, other: I2) -> Or<Self, I2, M>
    where
        I2: IntoInit<T, M, Error: Into<Self::Error>>,
    {
        or(self, other)
    }

    /// Provides a fallback initializer based on the error from this one.
    ///
    /// If initialization fails, the closure `f` is called with the error, and
    /// the returned initializer is used instead. This allows for
    /// error-dependent recovery.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{own, Own, init::*};
    ///
    /// let owned: Own<u32> = own!(try_with(|| u32::try_from(-1i32)).or_else(|err| {
    ///     println!("Initialization failed with error: {}", err);
    ///     value(42u32)
    /// }));
    /// assert_eq!(*owned, 42);
    /// ```
    fn or_else<F, I2>(self, f: F) -> OrElse<Self, F>
    where
        F: FnOnce(Self::Error) -> I2,
        I2: InitPin<T, Error: Into<Self::Error>>,
    {
        or_else(self, f)
    }

    /// Provides a fallback initializer if the primary one fails. The fallback
    /// initializer must be infallible.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{own, Own, init::*};
    ///
    /// let owned: Own<u32> = own!(value(10u32).unwrap_or(20u32));
    /// assert_eq!(*owned, 10);
    ///
    /// let failed: Own<u32> = own!(
    ///     try_with(|| u32::try_from(-1i32)).unwrap_or(30u32)
    /// );
    /// assert_eq!(*failed, 30);
    /// ```
    fn unwrap_or<M, I2>(self, other: I2) -> UnwrapOr<Self, I2, M>
    where
        I2: IntoInit<T, M, Error = Infallible>,
    {
        unwrap_or(self, other)
    }

    /// Provides a fallback initializer computed from the error of the primary
    /// one. The fallback initializer must be infallible.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{own, Own, init::*};
    ///
    /// let owned: Own<u32> = own!(
    ///     try_with(|| u32::try_from(-1i32)).
    ///         unwrap_or_else(|err| {
    ///             println!("Initialization failed with error: {}", err);
    ///             value(42u32)
    ///         })
    /// );
    /// assert_eq!(*owned, 42);
    /// ```
    fn unwrap_or_else<F, I2>(self, f: F) -> UnwrapOrElse<Self, F>
    where
        F: FnOnce(Self::Error) -> I2,
        I2: InitPin<T, Error = Infallible>,
    {
        unwrap_or_else(self, f)
    }

    /// Maps the error type of the initializer using a closure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{uninit, init::*};
    ///
    /// let mut uninit = uninit!(i32);
    /// let res = uninit.try_write(
    ///     try_with(|| -> Result<_, &str> { Err("initialization failed") })
    ///         .map_err(|e| format!("Error occurred: {}", e))
    /// );
    /// assert!(res.is_err());
    /// assert_eq!(
    ///     res.err().unwrap().error,
    ///     "Error occurred: initialization failed"
    /// );
    /// ```
    fn map_err<F, E2>(self, f: F) -> MapErr<Self, F>
    where
        F: FnOnce(Self::Error) -> E2,
    {
        map_err::<(), _, _, _, _>(self, f)
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
    /// Creates a new `InitError`.
    pub const fn new(error: E, place: Uninit<'a, T>) -> Self {
        InitError { error, place }
    }

    /// Converts this error into an `InitPinError` by adding a drop slot.
    pub fn into_pin<'b>(self, slot: DropSlot<'a, 'b, T>) -> InitPinError<'a, 'b, T, E> {
        InitPinError {
            error: self.error,
            place: self.place,
            slot,
        }
    }

    /// Maps the error contained in this `InitError` to a different error type.
    pub fn map<F, E2>(self, f: F) -> InitError<'a, T, E2>
    where
        F: FnOnce(E) -> E2,
    {
        InitError {
            error: f(self.error),
            place: self.place,
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

/// The result type for [initialization].
///
/// [initialization]: crate::init::Init::init
pub type InitResult<'a, T, E> = Result<Own<'a, T>, InitError<'a, T, E>>;

/// A trait for initializing a place with a value.
///
/// This trait is used to abstract over the different ways a place can be
/// initialized. See the implementors for more details.
///
/// # Safety
///
/// Unlike [the pinning variant](crate::init::InitPin), this trait does not have
/// the same restrictions regarding partially-initialized states. This is
/// because the values initialized through this trait are not pinned, and thus
/// do not have the same safety guarantees that pinned values require.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not an initializer for places of type `{T}`",
    label = "`{Self}` is not an initializer for type `{T}`"
)]
pub trait Init<T: ?Sized>: InitPin<T> {
    /// Initializes a place with a value.
    ///
    /// This method performs the actual initialization of an uninitialized
    /// place, creating an owned reference to the initialized value. Unlike
    /// `init_pin`, this does not pin the value.
    ///
    /// # Arguments
    ///
    /// * `place` - The uninitialized place to initialize
    ///
    /// # Returns
    ///
    /// Returns an [owned reference] on success, or an [`InitError`]
    /// containing the error and the failed place.
    ///
    /// [owned reference]: crate::Own
    fn init(self, place: Uninit<'_, T>) -> InitResult<'_, T, Self::Error>;

    /// Chains a closure to execute after successful initialization.
    ///
    /// This method allows you to perform additional setup on the initialized
    /// value. The closure receives a mutable reference to the newly
    /// initialized value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use placid::{own, Own, init::*};
    ///
    /// let owned: Own<Vec<_>> = own!(value(vec![1, 2, 3]).and(|v| v.push(4)));
    /// assert_eq!(*owned, vec![1, 2, 3, 4]);
    /// ```
    fn and<F: FnOnce(&mut T)>(self, f: F) -> And<Self, F> {
        and(self, f)
    }
}

/// A trait for converting a value into an initializer.
///
/// This trait is used to allow types to be directly used as initializers
/// without needing to wrap them in a specific initializer factory function.
#[diagnostic::on_unimplemented(
    message = "`{Self}` is not an initializer for places of type `{T}`",
    label = "`{Self}` is not an initializer for type `{T}`"
)]
pub trait IntoInit<T: ?Sized, Marker = ()>: Sized {
    /// Which kind of initializer this converts into?
    type Init: InitPin<T, Error = Self::Error>;
    /// The error type that can occur during initialization.
    type Error;

    /// Creates an initializer from this value.
    fn into_init(self) -> Self::Init;
}

impl<I: InitPin<T>, T: ?Sized> IntoInit<T> for I {
    type Init = I;
    type Error = I::Error;

    fn into_init(self) -> Self::Init {
        self
    }
}

/// Types that can be structurally initialized in a pinned place.
///
/// This trait is automatically implemented for types that derive [`InitPin`].
/// It provides a method to structurally initialize the type in a pinned
/// context.
///
/// Users should not implement this trait manually. It is intended to be
/// automatically derived to ensure correct behavior.
///
/// [`InitPin`]: macro@crate::InitPin
#[diagnostic::on_unimplemented(
    message = "`{Self}` cannot be structurally pin-initialized",
    label = "`{Self}` cannot be structurally pin-initialized",
    note = "`#[derive(InitPin)]` to enable structural pin-initialization for this type"
)]
pub trait StructuralInitPin<'b> {
    #[doc(hidden)]
    type __BuilderInitPin<'a: 'b>
    where
        Self: 'a;

    #[doc(hidden)]
    fn __builder_init_pin<'a>(
        place: Uninit<'a, Self>,
        slot: DropSlot<'a, 'b, Self>,
    ) -> Self::__BuilderInitPin<'a>
    where
        Self: 'a;
}

/// Types that can be structurally initialized in a place.
///
/// This trait is automatically implemented for types that derive [`Init`]. It
/// provides a method to structurally initialize the type in a non-pinned
/// context.
///
/// [`Init`]: macro@crate::Init
#[diagnostic::on_unimplemented(
    message = "`{Self}` cannot be structurally initialized",
    label = "`{Self}` cannot be structurally initialized",
    note = "`#[derive(Init)]` to enable structural initialization for this type"
)]
pub trait StructuralInit<'b>: StructuralInitPin<'b> {
    #[doc(hidden)]
    type __BuilderInit;

    #[doc(hidden)]
    fn __builder_init(place: Uninit<'b, Self>) -> Self::__BuilderInit;
}

// Factory functions & adapters

mod and;
pub use self::and::{And, AndPin, and, and_pin};

mod or;
pub use self::or::{
    MapErr, Or, OrElse, UnwrapOr, UnwrapOrElse, map_err, or, or_else, unwrap_or, unwrap_or_else,
};

mod raw;
pub use self::raw::{Raw, RawPin, TryRaw, TryRawPin, raw, raw_pin, try_raw, try_raw_pin};

mod slice;
pub use self::slice::{
    Repeat, RepeatWith, Slice, SliceError, Str, repeat, repeat_with, slice, str,
};

mod value;
pub use self::value::{TryWith, Value, With, try_with, value, with};

// Implemetations for the standard library types

mod imp;
