use core::convert::Infallible;

use crate::{
    Own, Uninit,
    init::{Init, InitError, InitPin, InitPinResult, IntoInit},
    pin::DropSlot,
};

/// Error type for slice initialization failures.
///
/// This structure is returned from slice initializers when the source and
/// target slices have mismatched lengths.
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

/// Initializes a slice by copying or cloning elements from a source slice.
///
/// This initializer is created by the [`slice()`] factory function or through
/// the [`IntoInit`] trait for slice types.
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

/// Initializes a slice by copying or cloning elements from a source slice.
///
/// This is used to initialize a pre-allocated slice by copying (for `Copy`
/// types) or cloning (for `Clone` types) elements from another slice. The
/// source and target slices must have the same length, or the initialization
/// will fail with a [`SliceError`].
///
/// This function is rarely used for direct initialization. Instead, use an
/// `&[T]` slice directly where an initializer is expected, as it implements
/// the [`IntoInit`] trait. Use this function for combining with other
/// initializers when needed.
///
/// # Examples
///
/// ```rust
/// use placid::{place, Uninit};
///
/// // Initialize a slice with integers
/// let source = [1, 2, 3, 4, 5];
/// let mut uninit: Uninit<[i32]> = place!(@uninit [i32; 5]);
/// let owned = uninit.write(&source[..]);
/// assert_eq!(&*owned, &[1, 2, 3, 4, 5]);
/// ```
///
/// Error on length mismatch:
/// ```rust
/// use placid::{place, Uninit};
///
/// let source = [1, 2, 3];
/// let mut uninit: Uninit<[i32]> = place!(@uninit [i32; 5]); // Different size
/// let result = uninit.try_write(&source[..]);
/// assert!(result.is_err()); // Fails because lengths don't match
/// ```
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

/// Initializes all elements of a slice with a single repeated value.
///
/// This initializer is created by the [`repeat()`] factory function.
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

/// Initializes all elements of a slice with a single repeated value.
///
/// This is used to initialize a slice where all elements are the same
/// value. The value is cloned for each position in the slice.
///
/// # Examples
///
/// Filling a slice with a repeated value:
/// ```rust
/// use placid::{place, Uninit, init::repeat};
///
/// let place: Uninit<[i32]> = place!(@uninit [i32; 3]);
/// let owned = place.write(repeat(5));
/// assert_eq!(*owned, [5, 5, 5]);
/// ```
pub const fn repeat<T: Clone>(value: T) -> Repeat<T> {
    Repeat(value)
}

/// Initializes a slice by calling a closure for each element.
///
/// This initializer is created by the [`repeat_with()`] factory function.
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

/// Initializes a slice by calling a closure for each element.
///
/// `RepeatWith` allows you to initialize a slice where each element is produced
/// by calling a closure with the element's index. This provides a flexible way
/// to create complex slice initializations.
///
/// # Examples
///
/// Creating a slice of indices:
/// ```rust
/// use placid::{place, Uninit, init::repeat_with};
///
/// let mut uninit: Uninit<[usize]> = place!(@uninit [usize; 5]);
/// let owned = uninit.write(repeat_with(|i| i * 2));
/// assert_eq!(&*owned, &[0, 2, 4, 6, 8]);
/// ```
pub const fn repeat_with<T, F>(f: F) -> RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    RepeatWith(f)
}
