use core::{
    convert::Infallible,
    mem::{self, MaybeUninit},
};

use crate::{
    Own, Uninit,
    init::{Init, InitError, InitPin, InitPinResult, InitResult, IntoInit},
    pin::DropSlot,
};

#[inline]
fn maybe_uninit_slice<T, const N: usize>(m: &mut MaybeUninit<[T; N]>) -> &mut [MaybeUninit<T>] {
    unsafe { &mut *(m.as_mut_ptr() as *mut [MaybeUninit<T>; N]) }
}

/// Error type for slice initialization failures.
///
/// This structure is returned from slice initializers when the source and
/// target slices have mismatched lengths.
#[derive(Debug, thiserror::Error, Clone, Copy, PartialEq)]
#[error("slice initialization error")]
pub struct SliceError;

trait SpecInitSlice<T> {
    fn init_slice(self, place: Uninit<'_, [T]>) -> InitResult<'_, [T], SliceError>;

    fn init_array<const N: usize>(
        self,
        place: Uninit<'_, [T; N]>,
    ) -> InitResult<'_, [T; N], SliceError>;
}

impl<T: Clone> SpecInitSlice<T> for &[T] {
    default fn init_slice(self, mut place: Uninit<'_, [T]>) -> InitResult<'_, [T], SliceError> {
        if place.len() != self.len() {
            return Err(InitError { error: SliceError, place });
        }

        place.write_clone_of_slice(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }

    default fn init_array<const N: usize>(
        self,
        mut place: Uninit<'_, [T; N]>,
    ) -> InitResult<'_, [T; N], SliceError> {
        if N != self.len() {
            return Err(InitError { error: SliceError, place });
        }

        maybe_uninit_slice(&mut place).write_clone_of_slice(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

impl<T: Copy> SpecInitSlice<T> for &[T] {
    fn init_slice(self, mut place: Uninit<'_, [T]>) -> InitResult<'_, [T], SliceError> {
        if place.len() != self.len() {
            return Err(InitError { error: SliceError, place });
        }

        place.write_copy_of_slice(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }

    fn init_array<const N: usize>(
        self,
        mut place: Uninit<'_, [T; N]>,
    ) -> InitResult<'_, [T; N], SliceError> {
        if N != self.len() {
            return Err(InitError { error: SliceError, place });
        }

        maybe_uninit_slice(&mut place).write_copy_of_slice(self);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

/// Initializes a slice by copying or cloning elements from a source slice.
///
/// This initializer is created by the [`slice()`] factory function or through
/// the [`IntoInit`] trait for slice types.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Slice<'a, T>(&'a [T]);

impl<T: Clone> InitPin<[T]> for Slice<'_, T> {
    type Error = SliceError;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> InitPinResult<'a, 'b, [T], SliceError> {
        match self.0.init_slice(place) {
            Ok(own) => Ok(Own::into_pin(own, slot)),
            Err(err) => Err(err.into_pin(slot)),
        }
    }
}

impl<T: Clone> Init<[T]> for Slice<'_, T> {
    fn init(self, place: Uninit<'_, [T]>) -> InitResult<'_, [T], SliceError> {
        self.0.init_slice(place)
    }
}

impl<T: Clone, const N: usize> InitPin<[T; N]> for Slice<'_, T> {
    type Error = SliceError;

    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, [T; N]>,
        slot: DropSlot<'a, 'b, [T; N]>,
    ) -> InitPinResult<'a, 'b, [T; N], SliceError> {
        match self.0.init_array(place) {
            Ok(own) => Ok(Own::into_pin(own, slot)),
            Err(err) => Err(err.into_pin(slot)),
        }
    }
}

impl<T: Clone, const N: usize> Init<[T; N]> for Slice<'_, T> {
    fn init(self, place: Uninit<'_, [T; N]>) -> InitResult<'_, [T; N], SliceError> {
        self.0.init_array(place)
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
/// use placid::{uninit, Uninit};
///
/// // Initialize a slice with integers
/// let source = [1, 2, 3, 4, 5];
/// let mut uninit = uninit!([i32; 5]);
/// let owned = uninit.write(&source[..]);
/// assert_eq!(&*owned, &[1, 2, 3, 4, 5]);
/// ```
///
/// Error on length mismatch:
/// ```rust
/// use placid::{uninit, Uninit};
///
/// let source = [1, 2, 3];
/// let mut uninit = uninit!([i32; 5]); // Different size
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

impl<'a, T: Clone, const N: usize> IntoInit<[T; N], Slice<'a, T>> for &'a [T] {
    type Init = Slice<'a, T>;
    type Error = SliceError;

    fn into_init(self) -> Self::Init {
        Slice(self)
    }
}

/// Initializes a `str` slice by copying from a source string slice.
///
/// This initializer is created by the [`str()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Str<'a>(&'a str);

impl InitPin<str> for Str<'_> {
    type Error = SliceError;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, str>,
        slot: DropSlot<'a, 'b, str>,
    ) -> InitPinResult<'a, 'b, str, SliceError> {
        if place.len() != self.0.len() {
            return Err(InitError { error: SliceError, place }.into_pin(slot));
        }

        let src = unsafe { mem::transmute::<&[u8], &[MaybeUninit<u8>]>(self.0.as_bytes()) };
        place.copy_from_slice(src);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl Init<str> for Str<'_> {
    fn init(self, mut place: Uninit<'_, str>) -> InitResult<'_, str, SliceError> {
        if place.len() != self.0.len() {
            return Err(InitError { error: SliceError, place });
        }

        let src = unsafe { mem::transmute::<&[u8], &[MaybeUninit<u8>]>(self.0.as_bytes()) };
        place.copy_from_slice(src);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

/// Initializes a `str` slice by copying from a source string slice.
///
/// This is used to initialize a pre-allocated `str` slice by copying the
/// contents from another string slice. The source and target slices must have
/// the same length, or the initialization will fail with a [`SliceError`].
///
/// Users typically do not need to call this function directly, as `&str`
/// implements the [`IntoInit`] trait. Use this function when combining with
/// other initializers.
///
/// # Examples
///
/// ```rust
/// use placid::{uninit, Uninit, init};
///
/// let source = "Hello, world!";
/// let mut uninit: Uninit<str> = uninit!([u8; 13]); // Pre-allocated for 13 bytes
/// let owned = uninit.write(init::str(source));
/// assert_eq!(&*owned, "Hello, world!");
/// ```
pub const fn str(s: &str) -> Str<'_> {
    Str(s)
}

impl<'b> IntoInit<str, Str<'b>> for &'b str {
    type Init = Str<'b>;
    type Error = SliceError;

    fn into_init(self) -> Self::Init {
        Str(self)
    }
}

/// Initializes all elements of a slice with a single repeated value.
///
/// This initializer is created by the [`repeat()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Repeat<T>(T);

impl<T: Clone> InitPin<[T]> for Repeat<T> {
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> InitPinResult<'a, 'b, [T], Infallible> {
        place.write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T: Clone> Init<[T]> for Repeat<T> {
    fn init(self, mut place: Uninit<'_, [T]>) -> InitResult<'_, [T], Infallible> {
        place.write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

impl<T: Clone, const N: usize> InitPin<[T; N]> for Repeat<T> {
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T; N]>,
        slot: DropSlot<'a, 'b, [T; N]>,
    ) -> InitPinResult<'a, 'b, [T; N], Infallible> {
        maybe_uninit_slice(&mut place).write_filled(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T: Clone, const N: usize> Init<[T; N]> for Repeat<T> {
    fn init(self, mut place: Uninit<'_, [T; N]>) -> InitResult<'_, [T; N], Infallible> {
        maybe_uninit_slice(&mut place).write_filled(self.0);
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
/// Filling an array with a repeated value:
///
/// ```rust
/// use placid::{uninit, Uninit, init::repeat};
///
/// let place = uninit!([i32; 3]);
/// let owned = place.write(repeat(5));
/// assert_eq!(*owned, [5, 5, 5]);
/// ```
pub const fn repeat<T: Clone>(value: T) -> Repeat<T> {
    Repeat(value)
}

/// Initializes a slice by calling a closure for each element.
///
/// This initializer is created by the [`repeat_with()`] factory function.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct RepeatWith<F>(F);

impl<T, F> InitPin<[T]> for RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> InitPinResult<'a, 'b, [T], Infallible> {
        place.write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T, F> Init<[T]> for RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    fn init(self, mut place: Uninit<'_, [T]>) -> InitResult<'_, [T], Infallible> {
        place.write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init() })
    }
}

impl<T, F, const N: usize> InitPin<[T; N]> for RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    type Error = Infallible;

    fn init_pin<'a, 'b>(
        self,
        mut place: Uninit<'a, [T; N]>,
        slot: DropSlot<'a, 'b, [T; N]>,
    ) -> InitPinResult<'a, 'b, [T; N], Infallible> {
        maybe_uninit_slice(&mut place).write_with(self.0);
        // SAFETY: The place is now initialized.
        Ok(unsafe { place.assume_init_pin(slot) })
    }
}

impl<T, F, const N: usize> Init<[T; N]> for RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    fn init(self, mut place: Uninit<'_, [T; N]>) -> InitResult<'_, [T; N], Infallible> {
        maybe_uninit_slice(&mut place).write_with(self.0);
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
/// Creating an array of indices:
/// ```rust
/// use placid::{uninit, Uninit, init::repeat_with};
///
/// let mut uninit = uninit!([usize; 5]);
/// let owned = uninit.write(repeat_with(|i| i * 2));
/// assert_eq!(&*owned, &[0, 2, 4, 6, 8]);
/// ```
pub const fn repeat_with<T, F>(f: F) -> RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    RepeatWith(f)
}
