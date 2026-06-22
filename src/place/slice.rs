use core::{
    iter::FusedIterator,
    marker::PhantomData,
    mem::{self, MaybeUninit},
    ptr::NonNull,
};

use crate::place::{PlaceRef, PlaceState};

#[allow(clippy::type_complexity)]
impl<'a, T, S: PlaceState> PlaceRef<'a, [T], S> {
    /// Returns the number of elements in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice: Own<[i32]> = own!([1, 2, 3]);
    /// assert_eq!(slice.len(), 3);
    /// ```
    #[inline]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the slice contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let empty_slice: Own<[i32]> = own!([]);
    /// assert!(empty_slice.is_empty());
    /// let non_empty_slice: Own<[i32]> = own!([1, 2, 3]);
    /// assert!(!non_empty_slice.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Converts the slice into an array place if it has exactly `N`
    /// items.
    ///
    /// If the slice does not have exactly `N` items, the original slice is
    /// returned as an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice: Own<[i32]> = own!([1, 2, 3]);
    /// let array = slice.into_array::<3>().unwrap();
    /// assert_eq!(*array, [1, 2, 3]);
    /// ```
    #[inline]
    pub const fn into_array<const N: usize>(
        self,
    ) -> Result<PlaceRef<'a, [T; N], S>, PlaceRef<'a, [T], S>> {
        if self.len() == N {
            let inner = self.inner;
            mem::forget(self);

            let first_ptr = inner.cast::<T>();
            let array_ptr = first_ptr.cast::<[T; N]>();

            let array = unsafe { PlaceRef::from_inner(array_ptr) };

            Ok(array)
        } else {
            Err(self)
        }
    }
}

macro_rules! impl_fwd {
    (@FWD $(#[$meta:meta])*
        $vis:vis fn $name:ident $([$($g:tt)*])? (self$(, $arg:ident: $arg_ty:ty)*)
            -> $ret_ty:ty
    ) => {
        $(#[$meta])*
        $vis fn $name $(<$($g)*>)? (self$(, $arg: $arg_ty)*) -> $ret_ty {
            self.into_slice().$name($($arg),*)
        }
    };
    (@FWD $(#[$meta:meta])*
        $vis:vis const fn $name:ident $([$($g:tt)*])? (self$(, $arg:ident: $arg_ty:ty)*)
            -> $ret_ty:ty
    ) => {
        $(#[$meta])*
        $vis const fn $name $(<$($g)*>)? (self$(, $arg: $arg_ty)*) -> $ret_ty {
            self.into_slice().$name($($arg),*)
        }
    };
    (@FWD $(#[$meta:meta])*
        $vis:vis const unsafe fn $name:ident $([$($g:tt)*])? (self$(, $arg:ident: $arg_ty:ty)*)
            -> $ret_ty:ty
    ) => {
        $(#[$meta])*
        $vis const unsafe fn $name $(<$($g)*>)? (self$(, $arg: $arg_ty)*) -> $ret_ty {
            unsafe { self.into_slice().$name($($arg),*) }
        }
    };

    (impl<$a:lifetime> $T:ident {$(
        $(#[$meta:meta])*
        $vis:vis M{$($m:tt)*} fn $name:ident $([$($g:tt)*])?
            ($this:ident @ self $(, $arg:ident: $arg_ty:ty)* $(,)?)
            -> $ret_ty:ty $body:block
    )*}) => {
        #[allow(clippy::type_complexity)]
        impl<$a, $T, S: PlaceState> PlaceRef<$a, [T], S> {
            $(
                $(#[$meta])*
                $vis $($m)* fn $name $(<$($g)*>)? (self$(, $arg: $arg_ty)*) -> $ret_ty {
                    let $this = self;
                    $body
                }
            )*
        }

        #[allow(clippy::type_complexity)]
        impl<$a, $T, const Q: usize, S: PlaceState> PlaceRef<$a, [T; Q], S> {
            $(impl_fwd!(@FWD $(#[$meta])*
                $vis $($m)* fn $name $([$($g)*])? (self$(, $arg: $arg_ty)*) -> $ret_ty
            );)*
        }
    };
}

impl_fwd!(impl<'a> T {
    /// Returns the first and all the rest of the elements in the slice, or
    /// `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3]);
    /// let (first, rest) = slice.split_first().unwrap();
    /// assert_eq!(*first, 1);
    /// assert_eq!(rest.len(), 2);
    /// ```
    #[inline]
    #[must_use]
    pub M{const} fn split_first(this @ self) -> Option<(PlaceRef<'a, T, S>, PlaceRef<'a, [T], S>)> {
        if !this.is_empty() {
            let inner = this.inner;
            mem::forget(this);

            let first_ptr = inner.cast::<T>();
            let rest_ptr = unsafe {
                NonNull::slice_from_raw_parts(first_ptr.add(1), inner.len().unchecked_sub(1))
            };

            let first = unsafe { PlaceRef::from_inner(first_ptr) };
            let rest = unsafe { PlaceRef::from_inner(rest_ptr) };

            Some((first, rest))
        } else {
            // An empty slice cannot contain any value that must be dropped, and `Own<[T]>`
            // itself doesn't have any extra dropping routines, so we can safely forget it
            // here.
            mem::forget(this);

            None
        }
    }

    /// Returns the last and all the rest of the elements in the slice, or
    /// `None` if it is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3]);
    /// let (last, rest) = slice.split_last().unwrap();
    /// assert_eq!(*last, 3);
    /// assert_eq!(rest.len(), 2);
    /// ```
    #[inline]
    #[must_use]
    pub M{const} fn split_last(this @ self) -> Option<(PlaceRef<'a, T, S>, PlaceRef<'a, [T], S>)> {
        if !this.is_empty() {
            let inner = this.inner;
            mem::forget(this);

            let first_ptr = inner.cast::<T>();
            let last_ptr = unsafe { first_ptr.add(inner.len().unchecked_sub(1)) };
            let rest_ptr =
                unsafe { NonNull::slice_from_raw_parts(first_ptr, inner.len().unchecked_sub(1)) };

            let last = unsafe { PlaceRef::from_inner(last_ptr) };
            let rest = unsafe { PlaceRef::from_inner(rest_ptr) };

            Some((last, rest))
        } else {
            // An empty slice cannot contain any value that must be dropped, and `Own<[T]>`
            // itself doesn't have any extra dropping routines, so we can safely forget it
            // here.
            mem::forget(this);

            None
        }
    }

    /// Returns an array place to the first `N` items in the slice and
    /// the remaining slice.
    ///
    /// If the slice is not at least `N` in length, the original slice is
    /// returned as an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3, 4]);
    /// let (chunk, rest) = slice.split_first_chunk::<2>().unwrap();
    /// assert_eq!(*chunk, [1, 2]);
    /// assert_eq!(rest.len(), 2);
    /// ```
    #[inline]
    pub M{const} fn split_first_chunk[const N: usize](
        this @ self
    ) -> Result<(PlaceRef<'a, [T; N], S>, PlaceRef<'a, [T], S>), PlaceRef<'a, [T], S>> {
        if this.len() >= N {
            let inner = this.inner;
            mem::forget(this);

            let first_ptr = inner.cast::<T>();
            let chunk_ptr = first_ptr.cast::<[T; N]>();
            let rest_ptr = unsafe {
                NonNull::slice_from_raw_parts(first_ptr.add(N), inner.len().unchecked_sub(N))
            };

            let chunk = unsafe { PlaceRef::from_inner(chunk_ptr) };
            let rest = unsafe { PlaceRef::from_inner(rest_ptr) };

            Ok((chunk, rest))
        } else {
            Err(this)
        }
    }

    /// Returns an array place to the last `N` items in the slice and
    /// the remaining slice.
    ///
    /// If the slice is not at least `N` in length, the original slice is
    /// returned as an error.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3, 4]);
    /// let (chunk, rest) = slice.split_last_chunk::<2>().unwrap();
    /// assert_eq!(*chunk, [3, 4]);
    /// assert_eq!(rest.len(), 2);
    /// ```
    #[inline]
    pub M{const} fn split_last_chunk[const N: usize](
        this @ self
    ) -> Result<(PlaceRef<'a, [T; N], S>, PlaceRef<'a, [T], S>), PlaceRef<'a, [T], S>> {
        if this.len() >= N {
            let inner = this.inner;
            mem::forget(this);

            let first_ptr = inner.cast::<T>();
            let chunk_ptr = unsafe { first_ptr.add(inner.len().unchecked_sub(N)).cast::<[T; N]>() };
            let rest_ptr =
                unsafe { NonNull::slice_from_raw_parts(first_ptr, inner.len().unchecked_sub(N)) };

            let chunk = unsafe { PlaceRef::from_inner(chunk_ptr) };
            let rest = unsafe { PlaceRef::from_inner(rest_ptr) };

            Ok((chunk, rest))
        } else {
            Err(this)
        }
    }

    /// Divides one slice into two at an index, without doing bounds checking.
    ///
    /// The first will contain all indices from `[0, mid)`, and the second will
    /// contain all indices from `[mid, len)`.
    ///
    /// # Safety
    ///
    /// Calling this method with an out-of-bounds index is undefined behavior
    /// even if the resulting slices are never used. The caller must ensure that
    /// `0 <= mid <= self.len()`.
    #[inline]
    #[must_use]
    pub M{const unsafe} fn split_at_unchecked(
        this @ self,
        mid: usize
    ) -> (PlaceRef<'a, [T], S>, PlaceRef<'a, [T], S>) {
        let inner = this.inner;
        mem::forget(this);

        let first_ptr = inner.cast::<T>();
        let first_slice_ptr = NonNull::slice_from_raw_parts(first_ptr, mid);
        let second_slice_ptr = unsafe {
            NonNull::slice_from_raw_parts(first_ptr.add(mid), inner.len().unchecked_sub(mid))
        };

        let first = unsafe { PlaceRef::from_inner(first_slice_ptr) };
        let second = unsafe { PlaceRef::from_inner(second_slice_ptr) };

        (first, second)
    }

    /// Divides one slice into two at an index.
    ///
    /// The first will contain all indices from `[0, mid)`, and the second will
    /// contain all indices from `[mid, len)`.
    ///
    /// If the slice is not at least `mid` in length, the original slice is
    /// returned as an error.
    ///
    /// # Examples
    ////
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3, 4]);
    /// let (first, second) = slice.split_at_checked(2).unwrap();
    /// assert_eq!(*first, [1, 2]);
    /// assert_eq!(*second, [3, 4]);
    /// ```
    #[inline]
    pub M{const} fn split_at_checked(
        this @ self,
        mid: usize
    ) -> Result<(PlaceRef<'a, [T], S>, PlaceRef<'a, [T], S>), PlaceRef<'a, [T], S>> {
        if this.len() >= mid {
            // SAFETY: We just checked that `mid` is a valid index into the slice, so the
            // resulting slices are guaranteed to be valid.
            Ok(unsafe { this.split_at_unchecked(mid) })
        } else {
            Err(this)
        }
    }

    /// Divides one slice into two at an index.
    ///
    /// The first will contain all indices from `[0, mid)`, and the second will
    /// contain all indices from `[mid, len)`.
    ///
    /// # Panics
    ///
    /// Panics if `mid > len`. For a non-panicking version, see
    /// [`split_at_checked`](PlaceRef::split_at_checked).
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3, 4]);
    /// let (first, second) = slice.split_at(2);
    /// assert_eq!(*first, [1, 2]);
    /// assert_eq!(*second, [3, 4]);
    /// ```
    #[inline]
    #[must_use]
    pub M{const} fn split_at(this @ self, mid: usize) -> (PlaceRef<'a, [T], S>, PlaceRef<'a, [T], S>) {
        assert!(mid <= this.len(), "index out of bounds");

        // SAFETY: We just checked that `mid` is a valid index into the slice, so the
        // resulting slices are guaranteed to be valid.
        unsafe { this.split_at_unchecked(mid) }
    }

    /// Splits the slice into a slice of `N`-element arrays, assuming that
    /// there's no remainder.
    ///
    /// # Safety
    ///
    /// This may only be called when
    ///
    /// - The slice splits exactly into `N`-element arrays, i.e. `self.len() % N
    ///   == 0`.
    /// - `N != 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3, 4]);
    /// let chunks = unsafe { slice.into_chunks_unchecked::<2>() };
    /// assert_eq!(*chunks, [[1, 2], [3, 4]]);
    /// ```
    #[inline]
    #[must_use]
    pub M{const unsafe} fn into_chunks_unchecked[const N: usize](this @ self)
        -> PlaceRef<'a, [[T; N]], S>
    {
        let inner = this.inner;
        mem::forget(this);

        let chunks_ptr = inner.cast::<[T; N]>();
        let chunks_len = unsafe { inner.len().unchecked_div_exact(N) };
        let chunks_slice_ptr = NonNull::slice_from_raw_parts(chunks_ptr, chunks_len);

        unsafe { PlaceRef::from_inner(chunks_slice_ptr) }
    }

    /// Splits the slice into a slice of `N`-element arrays, starting at the
    /// beginning of the slice, and a remainder slice with length strictly less
    /// than `N`.
    ///
    /// The remainder is meaningful in the division sense. Given `let (chunks,
    /// remainder) = slice.into_chunks()`, then:
    ///
    /// - `chunks.len() == slice.len() / N`
    /// - `remainder.len() == slice.len() % N`
    /// - `slice.len() == chunks.len() * N + remainder.len()`
    ///
    /// # Panics
    ///
    /// Panics if `N == 0`.
    ///
    /// Note that this check is against a const generic parameter, not a runtime
    /// value, and thus a particular monomorphization will either always panic
    /// or it will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3, 4, 5]);
    /// let (chunks, remainder) = slice.into_chunks::<2>();
    /// assert_eq!(*chunks, [[1, 2], [3, 4]]);
    /// assert_eq!(*remainder, [5]);
    /// ```
    #[inline]
    #[must_use]
    pub M{} fn into_chunks[const N: usize](this @ self)
        -> (PlaceRef<'a, [[T; N]], S>, PlaceRef<'a, [T], S>)
    {
        assert!(N != 0, "chunk size must be non-zero");

        let len_rounded_down = this.len() / N * N;
        // SAFETY: The rounded-down value is always the same or smaller than the
        // original length, and thus must be in-bounds of the slice.
        let (multiple_of_n, remainder) = unsafe { this.split_at_unchecked(len_rounded_down) };
        // SAFETY: We already panicked for zero, and ensured by construction
        // that the length of the subslice is a multiple of N.
        let array_slice = unsafe { multiple_of_n.into_chunks_unchecked() };
        (array_slice, remainder)
    }
});

impl<'a, T, const N: usize, S: PlaceState> PlaceRef<'a, [[T; N]], S> {
    /// Flattens the slice of arrays into a single slice.
    ///
    /// # Panics
    ///
    /// Panics if the length of the resulting slice would overflow `usize`.
    ///
    /// This is only possible when flattening a slice of arrays of zero-sized
    /// types, and thus tends to be irrelevant in practice. If `size_of::<T>() >
    /// 0`, this will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([[1, 2], [3, 4]]);
    /// let flat_slice = slice.flatten();
    /// assert_eq!(*flat_slice, [1, 2, 3, 4]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn flatten(self) -> PlaceRef<'a, [T], S> {
        let flat_len = if const { size_of::<T>() == 0 } {
            self.len().checked_mul(N).expect("slice len overflow")
        } else {
            // SAFETY: `self.len() * N` cannot overflow because `self` is
            // already in the address space.
            unsafe { self.len().unchecked_mul(N) }
        };

        let inner = self.inner;
        mem::forget(self);

        let flat_ptr = inner.cast::<T>();
        let flat_slice_ptr = NonNull::slice_from_raw_parts(flat_ptr, flat_len);

        unsafe { PlaceRef::from_inner(flat_slice_ptr) }
    }
}

impl<'a, T, const N: usize, const Q: usize, S: PlaceState> PlaceRef<'a, [[T; N]; Q], S> {
    /// Flattens the slice of arrays into a single slice.
    ///
    /// # Panics
    ///
    /// Panics if the length of the resulting slice would overflow `usize`.
    ///
    /// This is only possible when flattening a slice of arrays of zero-sized
    /// types, and thus tends to be irrelevant in practice. If `size_of::<T>() >
    /// 0`, this will never panic.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([[1, 2], [3, 4]]);
    /// let flat_slice = slice.flatten();
    /// assert_eq!(*flat_slice, [1, 2, 3, 4]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn flatten(self) -> PlaceRef<'a, [T], S> {
        self.into_slice().flatten()
    }
}

/// An iterator that yields maybe-owned references to the elements of a slice,
/// consuming the original slice reference.
///
/// # Examples
///
/// ```
/// use placid::prelude::*;
///
/// let slice = own!([1, 2, 3]);
/// let mut iter = slice.into_iter();
/// assert_eq!(*iter.next().unwrap(), 1);
/// assert_eq!(*iter.next().unwrap(), 2);
/// assert_eq!(*iter.next().unwrap(), 3);
/// assert!(iter.next().is_none());
/// ```
pub struct IntoIter<'a, T, S: PlaceState> {
    start: NonNull<T>,
    // `end` for non-ZSTs and `len` for ZSTs.
    end_or_len: *const T,
    _marker: PhantomData<(&'a mut MaybeUninit<PhantomData<[T]>>, S)>,
}

impl<'a, T, S: PlaceState> IntoIter<'a, T, S> {
    pub(crate) const fn new(place: PlaceRef<'a, [T], S>) -> Self {
        let inner = place.inner;
        mem::forget(place);

        let start = inner.cast::<T>();
        let end_or_len = if const { size_of::<T>() == 0 } {
            core::ptr::without_provenance(inner.len())
        } else {
            unsafe { start.as_ptr().add(inner.len()) }
        };

        Self {
            start,
            end_or_len,
            _marker: PhantomData,
        }
    }

    /// Converts the iterator back into a slice reference, consuming the
    /// iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let slice = own!([1, 2, 3]);
    /// let mut iter = slice.into_iter();
    /// assert_eq!(*iter.next().unwrap(), 1);
    /// let slice_again = iter.into_slice();
    /// assert_eq!(*slice_again, [2, 3]);
    /// ```
    #[inline]
    pub fn into_slice(self) -> PlaceRef<'a, [T], S> {
        let start = self.start;

        let len = self.len();
        let inner = NonNull::slice_from_raw_parts(start, len);

        mem::forget(self);

        // SAFETY: We are creating a reference from a valid pointer.
        unsafe { PlaceRef::from_inner(inner) }
    }
}

impl<'a, T, S: PlaceState> Drop for IntoIter<'a, T, S> {
    fn drop(&mut self) {
        unsafe { core::ptr::read(self).into_slice() };
    }
}

impl<'a, T, S: PlaceState> Iterator for IntoIter<'a, T, S> {
    type Item = PlaceRef<'a, T, S>;

    fn next(&mut self) -> Option<Self::Item> {
        if const { size_of::<T>() == 0 } {
            let len = self.end_or_len.addr();
            if len == 0 {
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(self.start) };
                self.end_or_len = core::ptr::without_provenance(len - 1);
                Some(uninit)
            }
        } else {
            // SAFETY: `self.end` is always non-null.
            if self.start == unsafe { NonNull::new_unchecked(self.end_or_len.cast_mut()) } {
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(self.start) };
                // SAFETY: We are advancing the pointer by one element, which is valid for the
                // original slice.
                unsafe { self.start = NonNull::new_unchecked(self.start.as_ptr().add(1)) };
                Some(uninit)
            }
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        if const { size_of::<T>() == 0 } {
            let len = self.end_or_len.addr();
            if n >= len {
                self.end_or_len = core::ptr::without_provenance(0);
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(self.start) };
                self.end_or_len = core::ptr::without_provenance(len - n - 1);
                Some(uninit)
            }
        } else {
            // SAFETY: `self.end` is always non-null.
            let end = unsafe { NonNull::new_unchecked(self.end_or_len.cast_mut()) };
            if n >= unsafe { end.offset_from_unsigned(self.start) } {
                self.start = end;
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let ptr = unsafe { self.start.as_ptr().add(n) };
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(NonNull::new_unchecked(ptr)) };
                // SAFETY: We are advancing the pointer by `n + 1` elements, which is valid for
                // the original slice.
                unsafe { self.start = NonNull::new_unchecked(ptr.add(1)) };
                Some(uninit)
            }
        }
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let len = if const { size_of::<T>() == 0 } {
            self.end_or_len.addr()
        } else {
            // SAFETY: `self.end` is always non-null.
            let end = unsafe { NonNull::new_unchecked(self.end_or_len.cast_mut()) };
            // SAFETY: We are calculating the length based on the original slice, which is
            // valid for the original slice.
            unsafe { end.offset_from_unsigned(self.start) }
        };
        (len, Some(len))
    }

    #[inline]
    fn last(mut self) -> Option<Self::Item> {
        self.next_back()
    }
}

impl<'a, T, S: PlaceState> DoubleEndedIterator for IntoIter<'a, T, S> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if const { size_of::<T>() == 0 } {
            let len = self.end_or_len.addr();
            if len == 0 {
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(self.start) };
                self.end_or_len = core::ptr::without_provenance(len - 1);
                Some(uninit)
            }
        } else {
            // SAFETY: `self.end` is always non-null.
            let end = unsafe { NonNull::new_unchecked(self.end_or_len.cast_mut()) };
            if self.start == end {
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let ptr = unsafe { end.as_ptr().sub(1) };
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(NonNull::new_unchecked(ptr)) };
                self.end_or_len = ptr;
                Some(uninit)
            }
        }
    }

    fn nth_back(&mut self, n: usize) -> Option<Self::Item> {
        if const { size_of::<T>() == 0 } {
            let len = self.end_or_len.addr();
            if n >= len {
                self.end_or_len = core::ptr::without_provenance(0);
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(self.start) };
                self.end_or_len = core::ptr::without_provenance(len - n - 1);
                Some(uninit)
            }
        } else {
            // SAFETY: `self.end` is always non-null.
            let end = unsafe { NonNull::new_unchecked(self.end_or_len.cast_mut()) };
            let remaining = unsafe { end.offset_from_unsigned(self.start) };
            if n >= remaining {
                self.end_or_len = self.start.as_ptr();
                None
            } else {
                // SAFETY: We are creating a reference from a valid pointer.
                let ptr = unsafe { end.as_ptr().sub(n + 1) };
                // SAFETY: We are creating a reference from a valid pointer.
                let uninit = unsafe { PlaceRef::from_inner(NonNull::new_unchecked(ptr)) };
                self.end_or_len = ptr;
                Some(uninit)
            }
        }
    }
}

impl<'a, T, S: PlaceState> ExactSizeIterator for IntoIter<'a, T, S> {}

impl<'a, T, S: PlaceState> FusedIterator for IntoIter<'a, T, S> {}

#[cfg(test)]
mod tests {
    use core::cell::Cell;

    use crate::{
        fixed::Fix,
        own,
        owned::{MoveToUninit, Own},
        uninit::Uninit,
    };

    #[test]
    fn test_iter_drop() {
        #[derive(Clone)]
        struct DropCounter<'a> {
            count: &'a Cell<usize>,
        }

        unsafe impl<'a> MoveToUninit for DropCounter<'a> {
            const IS_TRIVIAL: bool = true;

            fn move_to<'d>(from: Fix<Own<'_, Self>>, to: Uninit<'d, Self>) -> Fix<Own<'d, Self>> {
                to.write_fix(from.clone())
            }
        }

        impl<'a> Drop for DropCounter<'a> {
            fn drop(&mut self) {
                self.count.set(self.count.get() + 1);
            }
        }

        let drop_count = Cell::new(0);
        {
            let slice = own!([
                (0, DropCounter { count: &drop_count }),
                (1, DropCounter { count: &drop_count }),
                (2, DropCounter { count: &drop_count }),
            ]);
            let mut iter = slice.into_iter();
            assert_eq!(drop_count.get(), 0);
            assert_eq!(iter.next().unwrap().0, 0);
            assert_eq!(drop_count.get(), 1);
            assert_eq!(iter.next_back().unwrap().0, 2);
            assert_eq!(drop_count.get(), 2);
            // drop the iterator before consuming the last element, which should
            // drop the last element as well.
        }
        assert_eq!(drop_count.get(), 3);
    }
}
