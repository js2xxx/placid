use std::{cell::Cell, marker::PhantomData};

use placid::*;

#[derive(InitPin)]
struct TestStruct {
    a: u32,
    b: String,
}

#[test]
fn test_build() {
    let pown: POwn<TestStruct> = pown!(init_pin!(
        #[err_into(core::convert::Infallible)]
        TestStruct {
            a: init::value(99).and(|i| *i += 1),
            b: init::with(|| String::from("Hello")),
        }
    ));
    assert_eq!(pown.a, 100);
    assert_eq!(pown.b, "Hello");
}

#[test]
fn test_drop() {
    thread_local! {
        static DROPPED: Cell<bool> = const { Cell::new(false) };
    }

    struct DropTracker;
    impl Drop for DropTracker {
        fn drop(&mut self) {
            DROPPED.set(true);
        }
    }

    #[derive(Init)]
    struct TestDrop {
        tracker: DropTracker,
        bomb: u32,
    }

    let t = std::panic::catch_unwind(|| {
        let _: POwn<TestDrop> = pown!(init_pin!(TestDrop {
            tracker: || DropTracker,
            bomb: || -> u32 { panic!("Initialization failed") },
        }));
    });
    t.unwrap_err();
    assert!(DROPPED.replace(false));

    let t = std::panic::catch_unwind(|| {
        let _: Own<TestDrop> = own!(init!(TestDrop {
            tracker: init::value(DropTracker),
            bomb: || -> u32 { panic!("Initialization failed") },
        }));
    });
    t.unwrap_err();
    assert!(DROPPED.get());
}

#[derive(Init)]
pub struct GenericHygiene<Base, Ptr: core::fmt::Debug, Pin>
where
    Pin: Send + Sync + 'static,
{
    base: PhantomData<Base>,
    ptr: PhantomData<Ptr>,
    pub(crate) pin: PhantomData<Pin>,
}

#[derive(InitPin)]
struct Nested {
    #[pin]
    field: TestStruct,
    unpinned: u64,
}

#[test]
fn test_nested() {
    let pown: POwn<Nested> = pown!(init_pin!(Nested {
        #[pin]
        field: TestStruct {
            a: 7,
            b: || String::from("Nested"),
        },
        unpinned: 123,
    }));
    assert_eq!(pown.field.a, 7);
    assert_eq!(pown.field.b, "Nested");
    assert_eq!(pown.unpinned, 123);
}
