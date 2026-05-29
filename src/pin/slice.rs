use core::{mem, ptr::NonNull};

use crate::pin::POwn;

impl<'a, T, const N: usize> POwn<'a, [T; N]> {
    /// Converts the pinned & owned array into a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let array: POwn<[i32; 3]> = pown!([1, 2, 3]);
    /// let slice: POwn<[i32]> = array.to_slice();
    /// assert_eq!(*slice, [1, 2, 3]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn to_slice(self) -> POwn<'a, [T]> {
        let drop_flag = self.drop_flag;
        let inner = self.inner;
        mem::forget(self);

        let slice_ptr = inner.cast::<T>();
        let slice_slice_ptr = NonNull::slice_from_raw_parts(slice_ptr, N);

        POwn {
            drop_flag,
            inner: slice_slice_ptr,
        }
    }
}

/// Slice-specific methods for `POwn`.
///
/// Unlike `Own<[T]>`, `POwn<[T]>` does not implement methods that modify the
/// ownership range of the slice, such as `split_at` or `split_first`. This is
/// because its associsted drop slot must always be associated with the entire
/// slice, and thus it cannot be split into multiple independent `POwn`s.
impl<'a, T> POwn<'a, [T]> {
    /// Returns the number of elements in the slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let arr = pown!([1, 2, 3]);
    /// let slice: POwn<[i32]> = arr.to_slice();
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
    /// let empty_arr = pown!([]);
    /// let empty_slice: POwn<[i32]> = empty_arr.to_slice();
    /// assert!(empty_slice.is_empty());
    ///
    /// let non_empty_arr = pown!([1, 2, 3]);
    /// let non_empty_slice: POwn<[i32]> = non_empty_arr.to_slice();
    /// assert!(!non_empty_slice.is_empty());
    /// ```
    #[inline]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// Converts the slice into an powned array reference if it has exactly `N`
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
    /// let orig = pown!([1, 2, 3]);
    /// let slice: POwn<[i32]> = orig.to_slice();
    /// let array = slice.to_array::<3>().unwrap();
    /// assert_eq!(*array, [1, 2, 3]);
    /// ```
    #[inline]
    pub const fn to_array<const N: usize>(self) -> Result<POwn<'a, [T; N]>, Self> {
        if self.len() == N {
            let inner = self.inner;
            let drop_flag = self.drop_flag;
            mem::forget(self);

            let first_ptr = inner.cast::<T>();
            let array_ptr = first_ptr.cast::<[T; N]>();

            let array = POwn { drop_flag, inner: array_ptr };

            Ok(array)
        } else {
            Err(self)
        }
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
    /// let array = pown!([1, 2, 3, 4]);
    /// let slice: POwn<[i32]> = array.to_slice();
    /// let chunks = unsafe { slice.to_chunks_unchecked::<2>() };
    /// assert_eq!(*chunks, [[1, 2], [3, 4]]);
    /// ```
    #[inline]
    #[must_use]
    pub const unsafe fn to_chunks_unchecked<const N: usize>(self) -> POwn<'a, [[T; N]]> {
        let drop_flag = self.drop_flag;
        let inner = self.inner;
        mem::forget(self);

        let chunks_ptr = inner.cast::<[T; N]>();
        let chunks_len = unsafe { inner.len().unchecked_div_exact(N) };
        let chunks_slice_ptr = NonNull::slice_from_raw_parts(chunks_ptr, chunks_len);

        POwn {
            drop_flag,
            inner: chunks_slice_ptr,
        }
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
    /// Panics if `N == 0` or if `self.len() % N != 0`.
    ///
    /// # Examples
    ///
    /// ```
    /// use placid::prelude::*;
    ///
    /// let array = pown!([1, 2, 3, 4]);
    /// let slice: POwn<[i32]> = array.to_slice();
    /// let chunks = slice.to_chunks::<2>();
    /// assert_eq!(*chunks, [[1, 2], [3, 4]]);
    /// ```
    #[inline]
    #[must_use]
    pub fn to_chunks<const N: usize>(self) -> POwn<'a, [[T; N]]> {
        assert!(N != 0, "chunk size must be non-zero");
        assert!(
            self.len().is_multiple_of(N),
            "slice length must be a multiple of chunk size"
        );

        // SAFETY: The caller has guaranteed that `N != 0` and `self.len() % N == 0`.
        unsafe { self.to_chunks_unchecked::<N>() }
    }
}

impl<'a, T, const N: usize> POwn<'a, [[T; N]]> {
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
    /// let array = pown!([[1, 2], [3, 4]]);
    /// let slice: POwn<[[i32; 2]]> = array.to_slice();
    /// let flat_slice = slice.flatten();
    /// assert_eq!(*flat_slice, [1, 2, 3, 4]);
    /// ```
    #[inline]
    #[must_use]
    pub const fn flatten(self) -> POwn<'a, [T]> {
        let flat_len = if const { size_of::<T>() == 0 } {
            self.len().checked_mul(N).expect("slice len overflow")
        } else {
            // SAFETY: `self.len() * N` cannot overflow because `self` is
            // already in the address space.
            unsafe { self.len().unchecked_mul(N) }
        };

        let drop_flag = self.drop_flag;
        let inner = self.inner;
        mem::forget(self);

        let flat_ptr = inner.cast::<T>();
        let flat_slice_ptr = NonNull::slice_from_raw_parts(flat_ptr, flat_len);

        POwn { drop_flag, inner: flat_slice_ptr }
    }
}
