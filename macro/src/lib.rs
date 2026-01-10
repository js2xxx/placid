mod ctor;
mod derive;

#[proc_macro_derive(InitPin)]
pub fn derive_init_pin(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match derive::init_pin(&syn::parse_macro_input!(input as syn::DeriveInput)) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

#[proc_macro_derive(Init)]
pub fn derive_init(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match derive::init(&syn::parse_macro_input!(input as syn::DeriveInput)) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

#[proc_macro]
pub fn init_pin(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match ctor::init_pin(syn::parse_macro_input!(input as syn::Expr)) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}

#[proc_macro]
pub fn init(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    match ctor::init(syn::parse_macro_input!(input as syn::Expr)) {
        Ok(ts) => ts.into(),
        Err(e) => e.to_compile_error().into(),
    }
}
