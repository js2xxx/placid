use core::marker::Tuple;

use super::*;

impl<'a, Args: Tuple, F: FnOnce<Args> + ?Sized> FnOnce<Args> for Own<'a, F> {
    type Output = F::Output;

    extern "rust-call" fn call_once(self, args: Args) -> Self::Output {
        (*into_undrop_box(self)).call_once(args)
    }
}

impl<'a, Args: Tuple, F: FnMut<Args> + ?Sized> FnMut<Args> for Own<'a, F> {
    extern "rust-call" fn call_mut(&mut self, args: Args) -> Self::Output {
        (**self).call_mut(args)
    }
}

impl<'a, Args: Tuple, F: Fn<Args> + ?Sized> Fn<Args> for Own<'a, F> {
    extern "rust-call" fn call(&self, args: Args) -> Self::Output {
        (**self).call(args)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_fn() {
        let t = Box::new(1);
        let my_place: Own<dyn FnOnce(i32) -> i32> = own!(move |x| x + *t);
        let result = my_place(41);
        assert_eq!(result, 42);
    }
}
