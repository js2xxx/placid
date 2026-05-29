use core::{mem, ptr::NonNull};

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
    /// let array = slice.to_array::<3>().unwrap();
    /// assert_eq!(*array, [1, 2, 3]);
    /// ```
    #[inline]
    pub const fn to_array<const N: usize>(
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
            self.to_slice().$name($($arg),*)
        }
    };
    (@FWD $(#[$meta:meta])*
        $vis:vis const fn $name:ident $([$($g:tt)*])? (self$(, $arg:ident: $arg_ty:ty)*)
            -> $ret_ty:ty
    ) => {
        $(#[$meta])*
        $vis const fn $name $(<$($g)*>)? (self$(, $arg: $arg_ty)*) -> $ret_ty {
            self.to_slice().$name($($arg),*)
        }
    };
    (@FWD $(#[$meta:meta])*
        $vis:vis const unsafe fn $name:ident $([$($g:tt)*])? (self$(, $arg:ident: $arg_ty:ty)*)
            -> $ret_ty:ty
    ) => {
        $(#[$meta])*
        $vis const unsafe fn $name $(<$($g)*>)? (self$(, $arg: $arg_ty)*) -> $ret_ty {
            unsafe { self.to_slice().$name($($arg),*) }
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
    /// let chunks = unsafe { slice.to_chunks_unchecked::<2>() };
    /// assert_eq!(*chunks, [[1, 2], [3, 4]]);
    /// ```
    #[inline]
    #[must_use]
    pub M{const unsafe} fn to_chunks_unchecked[const N: usize](this @ self)
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
    /// remainder) = slice.to_chunks()`, then:
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
    /// let (chunks, remainder) = slice.to_chunks::<2>();
    /// assert_eq!(*chunks, [[1, 2], [3, 4]]);
    /// assert_eq!(*remainder, [5]);
    /// ```
    #[inline]
    #[must_use]
    pub M{} fn to_chunks[const N: usize](this @ self)
        -> (PlaceRef<'a, [[T; N]], S>, PlaceRef<'a, [T], S>)
    {
        assert!(N != 0, "chunk size must be non-zero");

        let len_rounded_down = this.len() / N * N;
        // SAFETY: The rounded-down value is always the same or smaller than the
        // original length, and thus must be in-bounds of the slice.
        let (multiple_of_n, remainder) = unsafe { this.split_at_unchecked(len_rounded_down) };
        // SAFETY: We already panicked for zero, and ensured by construction
        // that the length of the subslice is a multiple of N.
        let array_slice = unsafe { multiple_of_n.to_chunks_unchecked() };
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
        self.to_slice().flatten()
    }
}
