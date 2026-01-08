use core::{convert::Infallible, fmt};

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
pub trait InitPin<T: ?Sized, Marker = ()> {
    type Error;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>>;
}

/// A trait for initializing a place with a value.
///
/// This trait is used to abstract over the different ways a place can be
/// initialized. See the implementors for more details.
pub trait Init<T: ?Sized, Marker = ()>: InitPin<T, Marker> {
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>>;
}

pub enum FromValue {}

impl<T> InitPin<T, FromValue> for T {
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        (*place).write(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T> Init<T, FromValue> for T {
    fn init(self, mut place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        (*place).write(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub enum TryFromRawPin {}

impl<T: ?Sized, F, E> InitPin<T, TryFromRawPin> for F
where
    F: for<'a, 'b> FnOnce(
        Uninit<'a, T>,
        DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, E>>,
{
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        self(place, slot)
    }
}

pub enum FromRawPin {}

impl<T: ?Sized, F> InitPin<T, FromRawPin> for F
where
    F: for<'a, 'b> FnOnce(Uninit<'a, T>, DropSlot<'a, 'b, T>) -> POwn<'b, T>,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        Ok(self(place, slot))
    }
}

pub enum TryFromRaw {}

impl<T: ?Sized, F, E> InitPin<T, TryFromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, E>>,
{
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        self(place).map(|own| Own::into_pin(own, slot))
    }
}

impl<T: ?Sized, F, E> Init<T, TryFromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, E>>,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        self(place)
    }
}

pub enum FromRaw {}

impl<T: ?Sized, F> InitPin<T, FromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        Ok(Own::into_pin(self(place), slot))
    }
}

impl<T: ?Sized, F> Init<T, FromRaw> for F
where
    F: FnOnce(Uninit<'_, T>) -> Own<'_, T>,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        Ok(self(place))
    }
}

pub enum TryFromFn {}

impl<T, F, E> InitPin<T, TryFromFn> for F
where
    F: FnOnce() -> Result<T, E>,
{
    type Error = E;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        match self() {
            Ok(value) => Ok(place.write_pin(value, slot)),
            Err(e) => Err(Error { error: e, place }),
        }
    }
}

impl<T, F, E> Init<T, TryFromFn> for F
where
    F: FnOnce() -> Result<T, E>,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        match self() {
            Ok(value) => Ok(place.write(value)),
            Err(e) => Err(Error { error: e, place }),
        }
    }
}

pub enum FromFn {}

impl<T, F> InitPin<T, FromFn> for F
where
    F: FnOnce() -> T,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, T>,
        slot: DropSlot<'a, 'b, T>,
    ) -> Result<POwn<'b, T>, Error<'a, T, Self::Error>> {
        place.try_write_pin(self(), slot)
    }
}

impl<T, F> Init<T, FromFn> for F
where
    F: FnOnce() -> T,
{
    fn init(self, place: Uninit<'_, T>) -> Result<Own<'_, T>, Error<'_, T, Self::Error>> {
        place.try_write(self())
    }
}

#[derive(Debug, thiserror::Error)]
#[error("slice initialization error")]
pub struct SliceError;

trait SpecInitSlice<T> {
    fn init_slice(self, place: Uninit<'_, [T]>)
    -> Result<Own<'_, [T]>, Error<'_, [T], SliceError>>;
}

impl<T: Clone> SpecInitSlice<T> for &[T] {
    default fn init_slice(
        self,
        mut place: Uninit<'_, [T]>,
    ) -> Result<Own<'_, [T]>, Error<'_, [T], SliceError>> {
        if place.len() != self.len() {
            return Err(Error { error: SliceError, place });
        }

        place.write_clone_of_slice(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

impl<T: Copy> SpecInitSlice<T> for &[T] {
    fn init_slice(
        self,
        mut place: Uninit<'_, [T]>,
    ) -> Result<Own<'_, [T]>, Error<'_, [T], SliceError>> {
        if place.len() != self.len() {
            return Err(Error { error: SliceError, place });
        }

        place.write_copy_of_slice(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub enum FromSlice {}

impl<T, S> InitPin<[T], FromSlice> for S
where
    S: SpecInitSlice<T>,
{
    type Error = SliceError;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> Result<POwn<'b, [T]>, Error<'a, [T], Self::Error>> {
        self.init_slice(place).map(|own| Own::into_pin(own, slot))
    }
}

impl<T, S> Init<[T], FromSlice> for S
where
    S: SpecInitSlice<T>,
{
    fn init(self, place: Uninit<'_, [T]>) -> Result<Own<'_, [T]>, Error<'_, [T], Self::Error>> {
        self.init_slice(place)
    }
}

pub struct FromSliceElement<T>(pub(crate) T);

impl<T: Clone> InitPin<[T], FromSliceElement<T>> for FromSliceElement<T> {
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> Result<POwn<'b, [T]>, Error<'a, [T], Self::Error>> {
        place.write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T: Clone> Init<[T], FromSliceElement<T>> for FromSliceElement<T> {
    fn init(self, mut place: Uninit<'_, [T]>) -> Result<Own<'_, [T]>, Error<'_, [T], Self::Error>> {
        place.write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub struct FromSliceElementFn<F>(pub(crate) F);

impl<T, F> InitPin<[T], FromSliceElementFn<F>> for FromSliceElementFn<F>
where
    F: Fn(usize) -> T,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> Result<POwn<'b, [T]>, Error<'a, [T], Self::Error>> {
        place.write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T, F> Init<[T], FromSliceElementFn<F>> for FromSliceElementFn<F>
where
    F: Fn(usize) -> T,
{
    fn init(self, mut place: Uninit<'_, [T]>) -> Result<Own<'_, [T]>, Error<'_, [T], Self::Error>> {
        place.write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}
