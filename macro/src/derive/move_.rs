use proc_macro2::TokenStream;
use quote::{format_ident, quote};
use syn::{DeriveInput, Error, Fields, Member, punctuated::Punctuated};

pub fn move_(input: &DeriveInput) -> syn::Result<TokenStream> {
    // Extract generics and where clauses
    let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

    let ident = &input.ident;

    let variant = match &input.data {
        syn::Data::Struct(data) => data,
        syn::Data::Enum(e) => {
            return Err(Error::new_spanned(
                e.enum_token,
                "enums cannot be structurally derived",
            ));
        }
        syn::Data::Union(u) => {
            return Err(Error::new_spanned(
                u.union_token,
                "unions cannot be structurally derived",
            ));
        }
    };

    let fields = match &variant.fields {
        Fields::Named(v) => &v.named,
        Fields::Unnamed(v) => &v.unnamed,
        Fields::Unit => &Punctuated::new(),
    };

    let field_name: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| match &field.ident {
            Some(v) => Member::Named(v.clone()),
            None => Member::Unnamed(syn::Index::from(i)),
        })
        .collect();

    let field_name_src: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| match &field.ident {
            Some(v) => format_ident!("__src_{v}"),
            None => format_ident!("__src_{i}"),
        })
        .collect();

    let field_name_dst: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| match &field.ident {
            Some(v) => format_ident!("__dst_{v}"),
            None => format_ident!("__dst_{i}"),
        })
        .collect();

    let field_ty: Vec<_> = fields.iter().map(|field| &field.ty).collect();

    let krate = quote!(::placid);
    let trait_path = quote!(#krate::owned::MoveToUninit);
    let own = quote!(#krate::owned::Own);
    let uninit = quote!(#krate::uninit::Uninit);
    let munge = quote!(#krate::munge::munge);

    let dst = format_ident!("__to");
    let lt = quote!('__d);

    let where_clause = match where_clause {
        Some(wc) if wc.predicates.trailing_punct() => quote!(#wc #(#field_ty: #trait_path,)*),
        Some(wc) => quote!(#wc, #(#field_ty: #trait_path,)*),
        None => quote!(where #(#field_ty: #trait_path,)*),
    };

    Ok(quote! {
        #[automatically_derived]
        unsafe impl #impl_generics #trait_path for #ident #ty_generics
            #where_clause
        {
            const IS_TRIVIAL: bool = true #(&& <#field_ty as #trait_path>::IS_TRIVIAL)*;

            fn move_to<#lt>(
                from: #own<'_, Self>,
                mut #dst: #uninit<#lt, Self>,
            ) -> #own<#lt, Self> {
                if const { <Self as #trait_path>::IS_TRIVIAL } {
                    let this = core::mem::ManuallyDrop::new(from);
                    // SAFETY: We are moving the value out of `from` and into `#dst`.
                    return unsafe {
                        core::ptr::copy_nonoverlapping(
                            #own::as_ptr(&this),
                            #dst.as_mut_ptr(),
                            1,
                        );
                        #dst.assume_init()
                    };
                }

                #munge!(let Self { #(#field_name: #field_name_src,)* } = from);
                #munge!(let Self { #(#field_name: #field_name_dst,)* } = #dst.by_ref());

                // SAFETY: We are moving the values out of `from` and into `to` by each field.
                // The initialized fields would be properly dropped at their destination if a
                // panic occurs during the move.
                unsafe {
                    #(let #field_name_dst = #field_name_src.move_to(#field_name_dst);)*

                    ::core::mem::forget((#(#field_name_dst,)*));
                    #dst.assume_init()
                }
            }
        }
    })
}
