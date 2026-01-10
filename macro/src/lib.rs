use quote::ToTokens;

mod ctor;
mod derive;

#[proc_macro_derive(InitPin)]
pub fn derive_init_pin(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    match derive::init_pin(&input) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

#[proc_macro_derive(Init)]
pub fn derive_init(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as syn::DeriveInput);
    match derive::init(&input) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

#[proc_macro]
pub fn init_pin(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as ctor::Input);
    match ctor::init_pin(input) {
        Ok(ts) => ts.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}

#[proc_macro]
pub fn init(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let input = syn::parse_macro_input!(input as ctor::Input);
    match ctor::init(input) {
        Ok(ts) => ts.into_token_stream().into(),
        Err(e) => e.to_compile_error().into(),
    }
}
