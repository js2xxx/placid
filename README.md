# `placid` - Separated ownership and in-place construction

[![Cargo](https://img.shields.io/crates/v/placid?style=for-the-badge)](https://crates.io/crates/placid)
[![Documentation](https://img.shields.io/docsrs/placid?style=for-the-badge)](https://docs.rs/placid)
[![License](https://img.shields.io/crates/l/placid?style=for-the-badge)](https://github.com/js2xxx/placid?tab=readme-ov-file#license)

`placid` extends Rust's ownership model with owned and uninit references with pinning variants (semantically `&own T`, `&uninit T`, and `&pin own T` or `Pin<&own T>`). It also provides macros, traits, and functions for constructing and manipulating these types, achieving safe in-place construction.

## The problem

In Rust, the ownership of a value is typically bound to the value itself. In other words, there is no way to separate the ownership of a value from it.

This creates challenges in scenarios where:
- You need to construct large values in-place to build address-aware objects ergonomically;
- You want to transfer ownership of large objects without expensive `memcpy`s;

Traditional Rust forces you to construct values on the stack, then move them, which can be inefficient for large types. `placid` solves this by introducing owned and uninit references that carry full ownership through a reference.

## Features

- **Owned References (`&own T`)**: Carry exclusive ownership through a reference.
- **Pinned Owned References (`&pin own T`)**: Combine ownership with pinning guarantees for immovable types.
- **In-place Construction**: Construct complex types directly in their final location using `init!` and `init_pin!` macros.
- **Uninit References**: Work safely with uninitialized memory.
- **Safe Movement**: Transfer ownership out of smart pointers like `Box` without reallocating or moving the underlying data.


## Usage

Add `placid` to your `Cargo.toml`:

```toml
[dependencies]
placid = "<the current version>"
```

### Basic Ownership

Constructing an owned reference directly on the stack:

```rust
use placid::{Own, own, Init, init};

let simple = own!(42);
assert_eq!(*simple, 42);

#[derive(Init)]
struct LargeData {
    buffer: [u8; 1024],
}

fn process_owned(data: Own<LargeData>) {
    // The function owns the data and will drop it when done.
    println!("Processing: {} bytes", std::mem::size_of_val(&*data));
} // data is dropped here.

// In a real scenario, you'd construct this in-place rather than moving.
let owned = own!(init!(LargeData { buffer: init::repeat(42) }));
process_owned(owned);
```

### Pinned Types

For self-referential or pinned types:

```rust
use placid::{POwn, pown, InitPin, init};
use std::{pin::Pin, marker::PhantomPinned};

#[derive(InitPin)]
struct SelfRef {
    data: i32,
    data_ptr: *const i32,
    marker: PhantomPinned,
}

fn process_pinned(data: POwn<SelfRef>) {
    // The function owns the data and guarantees it won't move.
    // This is safe because the data is pinned in place.
}

let pinned = pown!(
    // Provide initial value for the struct.
    init::value(SelfRef {
        data: 42,
        data_ptr: std::ptr::null(),
        marker: PhantomPinned,
    })
    .and_pin(|this| unsafe {
        // SAFETY: We are initializing the self-referential pointer.
        let this = Pin::into_inner_unchecked(this);
        this.data_ptr = &this.data as *const i32;
    })
);
process_pinned(pinned);
```

### Moving Ownership

Moving out an owned reference from a regular smart pointer:

```rust
use placid::{Own, into_own, Place};

let boxed = Box::new(String::from("move me"));

let mut left; // Box<MaybeUninit<String>>
// Move out an owned reference from the Box. The original
// allocation is transferred to `left`, mutably borrowed
// by `own`.
let own = into_own!(left <- boxed);
assert_eq!(*own, "move me");

// Drops the String, but not the Box allocation.
drop(own);

// Now we can reuse the Box allocation.
let right = left.write(String::from("new value"));
assert_eq!(&*right, "new value");
```


## License

This project is licensed under either of:

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.


## References

- [`moveit`](https://crates.io/crates/moveit)
- [`pin-init`](https://crates.io/crates/pin-init)
- [The Algebra of Loans in Rust | 
Nadri's musings](https://nadrieril.github.io/blog/2025/12/21/the-algebra-of-loans-in-rust.html)
- [What is a place expression?](https://www.ralfj.de/blog/2024/08/14/places.html)
- The Rust official documentations
