use core::convert::Infallible;

use crate::{
    Own, Uninit,
    init::{Error, Init, InitPin},
    pin::{DropSlot, POwn},
};

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

impl<T: Clone> InitPin<[T], FromSlice> for &[T] {
    type Error = SliceError;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> Result<POwn<'b, [T]>, Error<'a, [T], Self::Error>> {
        self.init_slice(place).map(|own| Own::into_pin(own, slot))
    }
}

impl<T: Clone> Init<[T], FromSlice> for &[T] {
    fn init(self, place: Uninit<'_, [T]>) -> Result<Own<'_, [T]>, Error<'_, [T], Self::Error>> {
        self.init_slice(place)
    }
}

pub const fn slice<T: Clone>(s: &[T]) -> impl Init<[T], FromSlice, Error = SliceError> {
    s
}

pub struct FromSliceRepeat<T>(pub(crate) T);

impl<T: Clone> InitPin<[T], FromSliceRepeat<T>> for FromSliceRepeat<T> {
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

impl<T: Clone> Init<[T], FromSliceRepeat<T>> for FromSliceRepeat<T> {
    fn init(self, mut place: Uninit<'_, [T]>) -> Result<Own<'_, [T]>, Error<'_, [T], Self::Error>> {
        place.write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub const fn repeat<T: Clone>(value: T) -> impl Init<[T], FromSliceRepeat<T>, Error = Infallible> {
    FromSliceRepeat(value)
}

pub struct FromSliceRepeatWith<F>(pub(crate) F);

impl<T, F> InitPin<[T], FromSliceRepeatWith<F>> for FromSliceRepeatWith<F>
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

impl<T, F> Init<[T], FromSliceRepeatWith<F>> for FromSliceRepeatWith<F>
where
    F: Fn(usize) -> T,
{
    fn init(self, mut place: Uninit<'_, [T]>) -> Result<Own<'_, [T]>, Error<'_, [T], Self::Error>> {
        place.write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

pub const fn repeat_with<T, F>(f: F) -> impl Init<[T], FromSliceRepeatWith<F>, Error = Infallible>
where
    F: Fn(usize) -> T,
{
    FromSliceRepeatWith(f)
}
