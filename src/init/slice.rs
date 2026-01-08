use core::convert::Infallible;

use crate::{
    Own, Uninit,
    init::{Init, InitError, InitPin, InitPinResult, IntoInit},
    pin::DropSlot,
};

#[derive(Debug, thiserror::Error)]
#[error("slice initialization error")]
pub struct SliceError;

trait SpecInitSlice<T> {
    fn init_slice(
        self,
        place: Uninit<'_, [T]>,
    ) -> Result<Own<'_, [T]>, InitError<'_, [T], SliceError>>;
}

impl<T: Clone> SpecInitSlice<T> for &[T] {
    default fn init_slice(
        self,
        mut place: Uninit<'_, [T]>,
    ) -> Result<Own<'_, [T]>, InitError<'_, [T], SliceError>> {
        if place.len() != self.len() {
            return Err(InitError { error: SliceError, place });
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
    ) -> Result<Own<'_, [T]>, InitError<'_, [T], SliceError>> {
        if place.len() != self.len() {
            return Err(InitError { error: SliceError, place });
        }

        place.write_copy_of_slice(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub struct Slice<'a, T>(&'a [T]);

impl<T: Clone> InitPin for Slice<'_, T> {
    type Target = [T];
    type Error = SliceError;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> InitPinResult<'a, 'b, Self> {
        match self.0.init_slice(place) {
            Ok(own) => Ok(Own::into_pin(own, slot)),
            Err(err) => Err(err.into_pin(slot)),
        }
    }
}

impl<T: Clone> Init for Slice<'_, T> {
    fn init(self, place: Uninit<'_, [T]>) -> Result<Own<'_, [T]>, InitError<'_, [T], Self::Error>> {
        self.0.init_slice(place)
    }
}

pub const fn slice<T: Clone>(s: &[T]) -> Slice<'_, T> {
    Slice(s)
}

impl<'a, T: Clone> IntoInit<[T], Slice<'a, T>> for &'a [T] {
    type Init = Slice<'a, T>;
    type Error = SliceError;

    fn into_init(self) -> Self::Init {
        Slice(self)
    }
}

pub struct Repeat<T>(T);

impl<T: Clone> InitPin for Repeat<T> {
    type Target = [T];
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> InitPinResult<'a, 'b, Self> {
        place.write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T: Clone> Init for Repeat<T> {
    fn init(
        self,
        mut place: Uninit<'_, [T]>,
    ) -> Result<Own<'_, [T]>, InitError<'_, [T], Self::Error>> {
        place.write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub const fn repeat<T: Clone>(value: T) -> Repeat<T> {
    Repeat(value)
}

pub struct RepeatWith<F>(F);

impl<T, F> InitPin for RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    type Target = [T];
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> InitPinResult<'a, 'b, Self> {
        place.write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T, F> Init for RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    fn init(
        self,
        mut place: Uninit<'_, [T]>,
    ) -> Result<Own<'_, [T]>, InitError<'_, [T], Self::Error>> {
        place.write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub const fn repeat_with<T, F>(f: F) -> RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    RepeatWith(f)
}
