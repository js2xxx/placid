use core::{
    convert::Infallible,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ptr,
};

use crate::{
    init::{Init, InitError, InitPin, InitPinResult, InitResult, Initializer, IntoInitPin},
    pin::DropSlot,
    uninit::Uninit,
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
#[error("slice length mismatch")]
pub struct SliceError;

/// Initializes a slice by copying or cloning elements from a source slice.
///
/// This initializer is created by the [`slice()`] factory function or through
/// the [`IntoInitPin`] trait for slice types.
#[derive(Debug, PartialEq)]
pub struct Slice<'a, T>(&'a [T]);

impl<T> Initializer for Slice<'_, T> {
    type Error = SliceError;
}

impl<T: Clone> InitPin<[T]> for Slice<'_, T> {
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, [T]>,
        slot: DropSlot<'a, 'b, [T]>,
    ) -> InitPinResult<'a, 'b, [T], SliceError> {
        crate::init::clone(self.0)
            .init_pin(place, slot)
            .map_err(|e| e.map(|_| SliceError))
    }
}

impl<T: Clone> Init<[T]> for Slice<'_, T> {
    #[inline]
    fn init(self, place: Uninit<'_, [T]>) -> InitResult<'_, [T], SliceError> {
        crate::init::clone(self.0)
            .init(place)
            .map_err(|e| e.map(|_| SliceError))
    }
}

impl<T: Clone, const N: usize> InitPin<[T; N]> for Slice<'_, T> {
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, [T; N]>,
        slot: DropSlot<'a, 'b, [T; N]>,
    ) -> InitPinResult<'a, 'b, [T; N], SliceError> {
        let Some(arr) = self.0.as_array() else {
            return Err(InitError { error: SliceError, place }.into_pin(slot));
        };
        Ok(crate::init::clone(arr).init_pin(place, slot).unwrap())
    }
}

impl<T: Clone, const N: usize> Init<[T; N]> for Slice<'_, T> {
    #[inline]
    fn init(self, place: Uninit<'_, [T; N]>) -> InitResult<'_, [T; N], SliceError> {
        let Some(arr) = self.0.as_array() else {
            return Err(InitError { error: SliceError, place });
        };
        Ok(crate::init::clone::<[T; N]>(arr).init(place).unwrap())
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
/// `&[T]` slice directly where an initializer is expected, as `&[T]` can be
/// used directly as an initializer. Use this function for combining with other
/// initializers when needed.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
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
/// use placid::prelude::*;
///
/// let source = [1, 2, 3];
/// let mut uninit = uninit!([i32; 5]); // Different size
/// let result = uninit.try_write(&source[..]);
/// assert!(result.is_err()); // Fails because lengths don't match
/// ```
#[inline]
pub const fn slice<T: Clone>(s: &[T]) -> Slice<'_, T> {
    Slice(s)
}

impl<'a, T: Clone, const N: usize> IntoInitPin<[T; N], Slice<'a, T>> for &'a [T] {
    type Init = Slice<'a, T>;
    type Error = SliceError;

    #[inline]
    fn into_init(self) -> Self::Init {
        Slice(self)
    }
}

/// Initializes a `str` slice by copying from a source string slice.
///
/// This initializer is created by the [`str()`] factory function.
#[derive(Debug, PartialEq)]
pub struct Str<'a>(&'a str);

impl Initializer for Str<'_> {
    type Error = SliceError;
}

impl InitPin<str> for Str<'_> {
    #[inline]
    fn init_pin<'a, 'b>(
        self,
        place: Uninit<'a, str>,
        slot: DropSlot<'a, 'b, str>,
    ) -> InitPinResult<'a, 'b, str, SliceError> {
        crate::init::clone(self.0)
            .init_pin(place, slot)
            .map_err(|e| e.map(|_| SliceError))
    }
}

impl Init<str> for Str<'_> {
    #[inline]
    fn init(self, place: Uninit<'_, str>) -> InitResult<'_, str, SliceError> {
        crate::init::clone(self.0)
            .init(place)
            .map_err(|e| e.map(|_| SliceError))
    }
}

/// Initializes a `str` slice by copying from a source string slice.
///
/// This is used to initialize a pre-allocated `str` slice by copying the
/// contents from another string slice. The source and target slices must have
/// the same length, or the initialization will fail with a [`SliceError`].
///
/// Users typically do not need to call this function directly, as `&str` can be
/// used directly as an initializer. Use this function when combining with other
/// initializers.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let source = "Hello, world!";
/// let mut uninit: Uninit<str> = uninit!([u8; 13]); // Pre-allocated for 13 bytes
/// let owned = uninit.write(source);
/// assert_eq!(&*owned, "Hello, world!");
/// ```
#[inline]
pub const fn str(s: &str) -> Str<'_> {
    Str(s)
}

/// Initializes all elements of a slice with a single repeated value.
///
/// This initializer is created by the [`repeat()`] factory function.
#[derive(Debug, PartialEq)]
pub struct Repeat<T>(T);

impl<T> Initializer for Repeat<T> {
    type Error = Infallible;
}

impl<T: Clone> InitPin<[T]> for Repeat<T> {
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
/// use placid::prelude::*;
///
/// let place = uninit!([i32; 3]);
/// let owned = place.write(init::repeat(5));
/// assert_eq!(*owned, [5, 5, 5]);
/// ```
#[inline]
pub const fn repeat<T: Clone>(value: T) -> Repeat<T> {
    Repeat(value)
}

/// Initializes a slice by calling a closure for each element.
///
/// This initializer is created by the [`repeat_with()`] factory function.
#[derive(Debug, PartialEq)]
pub struct RepeatWith<F>(F);

impl<F> Initializer for RepeatWith<F> {
    type Error = Infallible;
}

impl<T, F> InitPin<[T]> for RepeatWith<F>
where
    F: Fn(usize) -> T,
{
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
/// use placid::prelude::*;
///
/// let mut uninit = uninit!([usize; 5]);
/// let owned = uninit.write(init::repeat_with(|i| i * 2));
/// assert_eq!(&*owned, &[0, 2, 4, 6, 8]);
/// ```
#[inline]
pub const fn repeat_with<T, F>(f: F) -> RepeatWith<F>
where
    F: Fn(usize) -> T,
{
    RepeatWith(f)
}

/// Initializes a slice by consuming an iterator.
///
/// This initializer is created by the [`from_iter()`] factory function.
#[derive(Debug, PartialEq)]
pub struct FromIter<I, T>(I, PhantomData<fn() -> T>);

/// The error type for `FromIter` initialization failures.
#[derive(Debug, thiserror::Error)]
#[error("iterator initialization failed")]
pub struct FromIterError(());

impl<I, T> Initializer for FromIter<I, T> {
    type Error = FromIterError;
}

#[inline]
fn collect_iter_slice<T, I>(uninit: &mut [MaybeUninit<T>], iter: I) -> Result<(), FromIterError>
where
    I: IntoIterator<Item = T>,
{
    let (_, remaining) = uninit.write_iter(iter);
    match remaining.len() {
        0 => Ok(()),
        len => {
            let init_len = uninit.len() - len;
            // SAFETY: We have initialized the first `init_len` elements, so we can safely
            // drop them.
            unsafe { uninit[..init_len].assume_init_drop() };
            Err(FromIterError(()))
        }
    }
}

#[inline]
fn collect_iter_array<T, const N: usize>(
    uninit: &mut MaybeUninit<[T; N]>,
    iter: impl IntoIterator<Item = T>,
) -> Result<(), FromIterError> {
    collect_iter_slice(maybe_uninit_slice(uninit), iter)
}

fn concat_str<'a, I>(uninit: &mut [MaybeUninit<u8>], iter: I) -> Result<(), FromIterError>
where
    I: IntoIterator<Item = &'a str>,
{
    let mut remaining = uninit.len();
    let mut dst = uninit.as_mut_ptr().cast::<u8>();

    for s in iter {
        let bytes = s.as_bytes();
        let len = remaining.min(bytes.len());

        // Checks if `len` is a valid code point boundary.
        if !s.is_char_boundary(len) {
            return Err(FromIterError(()));
        }

        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), dst, len) };
        dst = unsafe { dst.add(len) };
        remaining -= len;

        if remaining == 0 {
            return Ok(());
        }
    }

    Err(FromIterError(()))
}

fn collect_chars<I>(uninit: &mut [MaybeUninit<u8>], iter: I) -> Result<(), FromIterError>
where
    I: IntoIterator<Item = char>,
{
    let mut remaining = uninit.len();
    let mut dst = uninit.as_mut_ptr().cast::<u8>();

    for c in iter {
        if remaining < c.len_utf8() {
            return Err(FromIterError(()));
        }

        let mut buf = [0; 4];
        let bytes = c.encode_utf8(&mut buf).as_bytes();

        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), dst, bytes.len()) };
        dst = unsafe { dst.add(bytes.len()) };
        remaining -= bytes.len();

        if remaining == 0 {
            return Ok(());
        }
    }

    Err(FromIterError(()))
}

macro_rules! derive_from_iter {
    ($($(@[$($g:tt)*]:)? $item:ty => $ty:ty = $imp:ident),* $(,)?) => {$(
        impl<$($($g)*,)? __I> InitPin<$ty> for FromIter<__I, $item>
        where
            __I: IntoIterator<Item = $item>,
        {
            fn init_pin<'a, 'b>(
                self,
                mut place: Uninit<'a, $ty>,
                slot: DropSlot<'a, 'b, $ty>,
            ) -> InitPinResult<'a, 'b, $ty, FromIterError> {
                match $imp(&mut *place, self.0) {
                    Ok(()) => Ok(unsafe { place.assume_init_pin(slot) }),
                    Err(err) => Err(InitError { error: err, place }.into_pin(slot)),
                }
            }
        }

        impl<$($($g)*,)? __I> Init<$ty> for FromIter<__I, $item>
        where
            __I: IntoIterator<Item = $item>,
        {
            fn init(self, mut place: Uninit<'_, $ty>) -> InitResult<'_, $ty, FromIterError> {
                match $imp(&mut *place, self.0) {
                    Ok(()) => Ok(unsafe { place.assume_init() }),
                    Err(err) => Err(InitError { error: err, place }),
                }
            }
        }
    )*};
}

derive_from_iter! {
    @[T]:                 T => [T]    = collect_iter_slice,
    @[T, const N: usize]: T => [T; N] = collect_iter_array,

    @['t]: &'t str => str = concat_str,
              char => str = collect_chars,
}

/// Initializes a slice/str by collecting an iterator.
///
/// Unlike [`Extend`] and [`Iterator::collect_into`], which don't require all
/// the spare capacity to be filled, this initializer requires the iterator to
/// produce items enough to fill the entire target place. This behavior is
/// consistent with other slice initializers such as [`repeat`].
///
/// The source iterator will only be driven until the target place is fully
/// initialized. If it [references to] another longer iterator, the remaining
/// items will not be drained.
///
/// # Errors
///
/// The initialization fails if:
///
/// - The iterator produces fewer items than the length of the place, and;
/// - For `str` initialization, the target length is not a valid UTF-8 boundary
///   in the concatenated string.
///
/// Upon error, any elements that have already been initialized are properly
/// dropped to prevent memory leaks; the number of items produced by the
/// iterator is not specified.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let source = (1..).map(|x| x * 2);
/// let mut uninit = uninit!([i32; 5]);
/// let owned = uninit.write(init::from_iter(source));
/// assert_eq!(&*owned, &[2, 4, 6, 8, 10]);
///
/// let chars = ['H', 'e', 'l', 'l', 'o'];
/// let mut uninit_str: Uninit<str> = uninit!([u8; 5]);
/// let owned_str = uninit_str.write(init::from_iter(chars));
/// assert_eq!(&*owned_str, "Hello");
///
/// let failing_chars = ['P', '💣'];
/// let mut uninit_str: Uninit<str> = uninit!([u8; 3]);
/// // Fails because '💣' is 4 bytes and doesn't fit in the remaining space
/// uninit_str.try_write(init::from_iter(failing_chars)).unwrap_err();
/// ```
///
/// [references to]: Iterator::by_ref
#[inline]
pub const fn from_iter<I, T>(iter: I) -> FromIter<I, T>
where
    I: IntoIterator<Item = T>,
{
    FromIter(iter, PhantomData)
}

/// Initializes a slice by invoking an incremental closure.
///
/// This initializer is created by the [`incremental()`] factory function.
#[derive(Debug, PartialEq)]
pub struct Incremental<F, A: ?Sized, T>(F, PhantomData<fn(&mut A) -> T>);

impl<F, A: ?Sized, T> Initializer for Incremental<F, A, T> {
    type Error = Infallible;
}

fn write_inc_slice<T, F>(uninit: &mut [MaybeUninit<T>], mut f: F)
where
    F: FnMut(&mut [T]) -> T,
{
    struct Guard<'a, T> {
        slice: &'a mut [MaybeUninit<T>],
        initialized: usize,
    }

    impl<'a, T> Guard<'a, T> {
        fn initialized(&mut self) -> &mut [T] {
            let init_part = &mut self.slice[..self.initialized];
            // SAFETY: this raw sub-slice will contain only initialized objects.
            unsafe { init_part.assume_init_mut() }
        }

        fn write(&mut self, v: T) {
            self.slice[self.initialized].write(v);
            self.initialized += 1;
        }
    }

    impl<'a, T> Drop for Guard<'a, T> {
        fn drop(&mut self) {
            let initialized_part = &mut self.slice[..self.initialized];
            // SAFETY: this raw sub-slice will contain only initialized objects.
            unsafe {
                initialized_part.assume_init_drop();
            }
        }
    }

    let mut guard = Guard { slice: uninit, initialized: 0 };
    for _ in 0..guard.slice.len() {
        let next = f(guard.initialized());
        guard.write(next);
    }
    mem::forget(guard);
}

#[inline]
fn write_inc_array<T, F, const N: usize>(uninit: &mut MaybeUninit<[T; N]>, f: F)
where
    F: FnMut(&mut [T]) -> T,
{
    write_inc_slice(maybe_uninit_slice(uninit), f)
}

fn write_inc_str<'t, F>(uninit: &mut [MaybeUninit<u8>], mut f: F)
where
    F: FnMut(&mut str) -> &'t str,
{
    let mut initialized = 0;
    let total = uninit.len();
    let dst = uninit.as_mut_ptr().cast::<u8>();

    loop {
        let next = f(unsafe {
            let init = core::slice::from_raw_parts_mut(dst, initialized);
            core::str::from_utf8_unchecked_mut(init)
        });

        let bytes = next.as_bytes();
        let len = (total - initialized).min(bytes.len());

        // Checks if `len` is a valid code point boundary.
        assert!(
            next.is_char_boundary(len),
            "invalid UTF-8 boundary in incremental initialization"
        );

        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), dst.add(initialized), len) };
        initialized += len;

        if initialized == total {
            break;
        }
    }
}

fn write_inc_chars<F>(uninit: &mut [MaybeUninit<u8>], mut f: F)
where
    F: FnMut(&mut str) -> char,
{
    let mut initialized = 0;
    let total = uninit.len();
    let dst = uninit.as_mut_ptr().cast::<u8>();

    loop {
        let next = f(unsafe {
            let init = core::slice::from_raw_parts_mut(dst, initialized);
            core::str::from_utf8_unchecked_mut(init)
        });

        assert!(
            initialized + next.len_utf8() <= total,
            "not enough space for next char in incremental initialization"
        );

        let mut buf = [0; 4];
        let bytes = next.encode_utf8(&mut buf).as_bytes();

        unsafe { ptr::copy_nonoverlapping(bytes.as_ptr(), dst.add(initialized), bytes.len()) };
        initialized += bytes.len();

        if initialized == total {
            break;
        }
    }
}

macro_rules! derive_incremental {
    (@COERCED $ty:ty |[$coerced:ty]) => { $coerced };
    (@COERCED $ty:ty) => { $ty };
    ($($(@[$($g:tt)*]:)? $item:ty => $ty:ty $(|[$coerced:ty])? = $imp:ident),* $(,)?) => {$(
        impl<$($($g)*,)? __F> InitPin<$ty> for Incremental<
            __F,
            derive_incremental!(@COERCED $ty $(|[$coerced])?),
            $item,
        >
        where
            __F: FnMut(
                &mut derive_incremental!(@COERCED $ty $(|[$coerced])?)
            ) -> $item,
        {
            fn init_pin<'a, 'b>(
                self,
                mut place: Uninit<'a, $ty>,
                slot: DropSlot<'a, 'b, $ty>,
            ) -> InitPinResult<'a, 'b, $ty, Infallible> {
                $imp(&mut *place, self.0);
                Ok(unsafe { place.assume_init_pin(slot) })
            }
        }

        impl<$($($g)*,)? __F> Init<$ty> for Incremental<
            __F,
            derive_incremental!(@COERCED $ty $(|[$coerced])?),
            $item,
        >
        where
            __F: FnMut(
                &mut derive_incremental!(@COERCED $ty $(|[$coerced])?)
            ) -> $item,
        {
            fn init(self, mut place: Uninit<'_, $ty>) -> InitResult<'_, $ty, Infallible> {
                $imp(&mut *place, self.0);
                Ok(unsafe { place.assume_init() })
            }
        }
    )*};
}

derive_incremental! {
    @[T]:                 T => [T]           = write_inc_slice,
    @[T, const N: usize]: T => [T; N] |[[T]] = write_inc_array,

    @['t]: &'t str => str = write_inc_str,
              char => str = write_inc_chars,
}

/// Initializes a slice/str by invoking an incremental closure.
///
/// This is used to initialize a slice/str by repeatedly calling a closure that
/// produces the next element based on the elements initialized so far. This
/// allows for complex initialization patterns that depend on previously
/// initialized elements.
///
/// # Examples
///
/// ```rust
/// use placid::prelude::*;
///
/// let mut uninit = uninit!([Box<i32>; 5]);
/// let owned = uninit.write(init::incremental(|init: &mut [Box<i32>]| {
///     match init {
///         [] => Box::new(1),
///         [.., last] => Box::new(**last * 2),
///     }
/// }));
/// assert!(owned.iter().map(|x| **x).eq([1, 2, 4, 8, 16]));
///
/// let mut uninit_str: Uninit<str> = uninit!([u8; 11]);
/// let owned_str = uninit_str.write(init::incremental(|init: &mut str| {
///     match &*init {
///         "" => "Hello",
///         s => if s.len() <= 5 {
///             init.make_ascii_uppercase();
///             " "
///         } else {
///             "world!"
///         },
///     }
/// }));
/// // The "!" is truncated because the total length is only 11 bytes.
/// assert_eq!(&*owned_str, "HELLO world");
/// ```
#[inline]
pub const fn incremental<A: ?Sized, T, F>(f: F) -> Incremental<F, A, T>
where
    F: FnMut(&mut A) -> T,
{
    Incremental(f, PhantomData)
}
