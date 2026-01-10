use proc_macro2::{Span, TokenStream};
use quote::{ToTokens, format_ident, quote, quote_spanned};
use syn::{
    DeriveInput, Error, Fields, GenericParam, Generics, Lifetime, Member, Result, TraitBound,
    TraitBoundModifier, TypeParamBound, parse_quote, punctuated::Punctuated,
};

fn opt_iter<T>(v: &Option<T>) -> &[T] {
    match v {
        Some(v) => std::slice::from_ref(v),
        None => &[],
    }
}

fn derive(input: &DeriveInput, pinned: bool) -> std::result::Result<TokenStream, Error> {
    // Extract generics and where clauses
    let Generics {
        params: generics, where_clause, ..
    } = &input.generics;
    let generics: Vec<_> = generics
        .into_iter()
        .map(|x| {
            let mut x = x.clone();
            match &mut x {
                GenericParam::Lifetime(_) => (),
                GenericParam::Type(t) => {
                    t.default = None;

                    // Need to remove ?Sized bound.
                    let bounds = std::mem::take(&mut t.bounds);
                    t.bounds = bounds
                        .into_iter()
                        .filter(|b| {
                            !matches!(
                                b,
                                TypeParamBound::Trait(TraitBound {
                                    modifier: TraitBoundModifier::Maybe(_),
                                    ..
                                })
                            )
                        })
                        .collect();
                }
                GenericParam::Const(c) => c.default = None,
            }
            x
        })
        .collect();

    let ty_generics: Vec<_> = generics
        .iter()
        .map(|x| -> &dyn ToTokens {
            match x {
                GenericParam::Lifetime(l) => &l.lifetime,
                GenericParam::Type(t) => &t.ident,
                GenericParam::Const(c) => &c.ident,
            }
        })
        .collect();

    let vis = &input.vis;
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

    let (fields, named) = match &variant.fields {
        Fields::Named(v) => (&v.named, true),
        Fields::Unnamed(v) => (&v.unnamed, false),
        Fields::Unit => (&Punctuated::new(), false),
    };

    let field_name: Vec<_> = fields
        .iter()
        .enumerate()
        .map(|(i, field)| match &field.ident {
            Some(v) => Member::Named(v.clone()),
            None => Member::Unnamed(i.into()),
        })
        .collect();

    let is_pinned: Vec<_> = fields
        .iter()
        .map(|field| field.attrs.iter().any(|attr| attr.path().is_ident("pin")))
        .collect();

    // Create identifier names that are unlikely to be used.
    let typestate_name: Vec<_> = field_name
        .iter()
        .enumerate()
        .map(|(f, _)| format_ident!("__C{}", f))
        .collect();

    let this_lifetime: Lifetime = parse_quote!('__this);
    let pin_lifetime: Option<Lifetime> = pinned.then(|| parse_quote!('__pin));
    let pin_lifetime_q = opt_iter(&pin_lifetime);
    let init_lifetime = pin_lifetime.as_ref().unwrap_or(&this_lifetime);

    let error_ident = format_ident!("__E");
    let arg_ident = format_ident!("__A");
    let marker_ident = format_ident!("__M");
    let builder_ident = if pinned {
        format_ident!("InitPin{ident}")
    } else {
        format_ident!("Init{ident}")
    };

    let init_error = if pinned {
        format_ident!("InitPinError")
    } else {
        format_ident!("InitError")
    };

    let bound_generics: Vec<_> = generics
        .iter()
        .map(|g| match g.clone() {
            GenericParam::Type(mut t) => {
                t.bounds.push(parse_quote!(#init_lifetime));
                GenericParam::Type(t)
            }
            other => other,
        })
        .collect();

    // Hygiene for local variables.
    let mixed_site = Span::mixed_site();

    let mut builder = Vec::new();

    builder.push({
        let (typestate_impl, typestate_ty, drop_impl) = if named {
            (
                quote_spanned! { mixed_site => #(const #typestate_name: bool,)* },
                quote_spanned! { mixed_site => #(#typestate_name,)* },
                quote_spanned! { mixed_site => #(
                    if #typestate_name {
                        // SAFETY: Typestate ensures that we are only dropping
                        //         initialized value.
                        unsafe {
                            let ptr = ::core::ptr::addr_of_mut!((*base).#field_name);
                            ptr.drop_in_place();
                        }
                    }
                )*},
            )
        } else {
            (
                quote_spanned! { mixed_site => const __C: usize, },
                quote_spanned! { mixed_site => __C, },
                quote_spanned! { mixed_site => #(
                    if __C > #field_name {
                        // SAFETY: Typestate ensures that we are only dropping
                        //         initialized value.
                        unsafe {
                            let ptr = ::core::ptr::addr_of_mut!((*base).#field_name);
                            ptr.drop_in_place();
                        }
                    }
                )*},
            )
        };

        let slot_def = pin_lifetime.as_ref().map(|pin_lifetime| {
            quote_spanned! { mixed_site =>
                slot: ::placid::pin::DropSlot<
                    #this_lifetime,
                    #pin_lifetime,
                    #ident<#(#ty_generics),*>
                >,
            }
        });

        let slot_assign = pinned.then(|| {
            quote_spanned! { mixed_site =>
                slot: unsafe { core::ptr::read(&this.slot) },
            }
        });

        quote_spanned! { mixed_site =>
            #[doc(hidden)]
            #vis struct #builder_ident<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#generics,)*
                #typestate_impl
            > #where_clause {
                uninit: ::placid::Uninit<#this_lifetime, #ident<#(#ty_generics),*>>,
                #slot_def
            }

            impl<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#generics,)*
                #typestate_impl
            > #builder_ident<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#ty_generics,)*
                #typestate_ty
            > #where_clause {
                #[doc(hidden)]
                #[inline]
                unsafe fn __drop_init(&mut self) {
                    let base = self.uninit.as_mut_ptr();
                    #drop_impl
                }

                #[doc(hidden)]
                #[inline]
                fn __err<#error_ident>(
                    self,
                    err: #error_ident,
                ) -> ::placid::init::#init_error<
                    #this_lifetime,
                    #(#pin_lifetime_q,)*
                    #ident<#(#ty_generics),*>,
                    #error_ident,
                > {
                    let mut this = ::core::mem::ManuallyDrop::new(self);
                    unsafe { this.__drop_init() };
                    ::placid::init::#init_error {
                        error: err,
                        place: unsafe { core::ptr::read(&this.uninit) },
                        #slot_assign
                    }
                }
            }

            impl<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#generics,)*
                #typestate_impl
            > Drop for #builder_ident<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#ty_generics,)*
                #typestate_ty
            > #where_clause {
                #[inline]
                fn drop(&mut self) {
                    unsafe { self.__drop_init() };
                }
            }
        }
    });

    for (i, field) in fields.iter().enumerate() {
        let field_name_cur = &field_name[i];
        let field_pinned = is_pinned[i];
        let vis = &field.vis;
        let ty = &field.ty;

        let (typestate_impl, typestate_ty_pre, typestate_ty_post, fn_name) = if named {
            let typestate_name_before = &typestate_name[0..i];
            let typestate_name_after = &typestate_name[i + 1..];

            (
                quote_spanned! { mixed_site =>
                    #(const #typestate_name_before: bool,)*
                    #(const #typestate_name_after: bool,)*
                },
                quote_spanned! { mixed_site =>
                    #(#typestate_name_before,)*
                    false,
                    #(#typestate_name_after,)*
                },
                quote_spanned! {mixed_site =>
                    #(#typestate_name_before,)*
                    true,
                    #(#typestate_name_after,)*
                },
                quote_spanned! { mixed_site => #field_name_cur },
            )
        } else {
            let next = i + 1;
            (
                quote_spanned! { mixed_site => },
                quote_spanned! { mixed_site => #i, },
                quote_spanned! { mixed_site => #next, },
                quote_spanned! { mixed_site => __next },
            )
        };

        let init_bound = if pinned && field_pinned {
            quote_spanned! { mixed_site => }
        } else {
            quote_spanned! { mixed_site =>
                Init: ::placid::init::Init<#ty>,
            }
        };

        let slot_creation = pin_lifetime.as_ref().map(|pin_lifetime| {
            quote_spanned! { mixed_site =>
                let mut slot = ::core::mem::ManuallyDrop::new(
                    ::placid::pin::DroppingSlot::new()
                );
                // SAFETY: We actually forget `slot` since the lifetime of
                // the object returns back to the builder itself instead of `POwn`.
                let slot_ref = unsafe {
                    ::core::mem::transmute::<
                        ::placid::pin::DropSlot<'_, '_, #ty>,
                        ::placid::pin::DropSlot<
                            #this_lifetime,
                            #pin_lifetime,
                            #ty,
                        >,
                    >(::placid::pin::DropSlot::new_unchecked(&mut slot))
                };
            }
        });

        let init_call = if pinned && field_pinned {
            quote_spanned! { mixed_site =>
                init.init_pin(field_place, slot_ref)
            }
        } else {
            quote_spanned! { mixed_site =>
                init.init(field_place)
            }
        };

        let func = quote_spanned! { mixed_site =>
            #[inline]
            #vis fn #fn_name<
                #arg_ident,
                #error_ident,
                #marker_ident,
            >(
                mut self,
                init: #arg_ident,
            ) -> Result<
                #builder_ident<
                    #this_lifetime,
                    #(#pin_lifetime_q,)*
                    #(#ty_generics,)*
                    #typestate_ty_post
                >,
                ::placid::init::#init_error<
                    #this_lifetime,
                    #(#pin_lifetime_q,)*
                    #ident<#(#ty_generics),*>,
                    #error_ident,
                >,
            >
            where
                #arg_ident: ::placid::init::IntoInit<
                    #ty,
                    #marker_ident,
                    #init_bound
                    Error = #error_ident,
                >,
            {
                use ::placid::{InitPin, Init};
                let init = init.into_init();

                #slot_creation

                // SAFETY: We are initializing the field here.
                let field_place = unsafe {
                    let base = self.uninit.as_mut_ptr();
                    let field_ptr = &raw mut (*base).#field_name_cur;
                    ::placid::Uninit::from_raw(field_ptr)
                };

                match #init_call {
                    Ok(own) => {
                        ::core::mem::forget(own);
                        Ok(unsafe {
                            ::core::mem::transmute::<
                                #builder_ident<
                                    #this_lifetime,
                                    #(#pin_lifetime_q,)*
                                    #(#ty_generics,)*
                                    #typestate_ty_pre
                                >,
                                #builder_ident<
                                    #this_lifetime,
                                    #(#pin_lifetime_q,)*
                                    #(#ty_generics,)*
                                    #typestate_ty_post
                                >,
                            >(self)
                        })
                    }
                    Err(err) => Err(self.__err(err.error)),
                }
            }
        };

        builder.push(quote_spanned! { mixed_site =>
            impl<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#generics,)*
                #typestate_impl
            > #builder_ident<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#ty_generics,)*
                #typestate_ty_pre
            > #where_clause {
                #func
            }
        });
    }

    builder.push({
        let (typestate_ty_pre, typestate_ty_post) = if named {
            let all_true: Vec<_> = field_name.iter().map(|_| quote!(true)).collect();
            let all_false: Vec<_> = field_name.iter().map(|_| quote!(false)).collect();

            (
                quote_spanned! { mixed_site => #(#all_false,)* },
                quote_spanned! { mixed_site => #(#all_true,)* },
            )
        } else {
            let len = field_name.len();
            (
                quote_spanned! { mixed_site => 0, },
                quote_spanned! { mixed_site => #len, },
            )
        };

        let result_ty = if let Some(pin_lifetime) = &pin_lifetime {
            quote_spanned! { mixed_site =>
                ::placid::POwn<
                    #pin_lifetime,
                    #ident<#(#ty_generics),*>,
                >
            }
        } else {
            quote_spanned! { mixed_site =>
                ::placid::Own<
                    #this_lifetime,
                    #ident<#(#ty_generics),*>,
                >
            }
        };

        let assume_init = if pinned {
            quote_spanned! { mixed_site =>
                let uninit = core::ptr::read(&this.uninit);
                let slot = core::ptr::read(&this.slot);
                uninit.assume_init_pin(slot)
            }
        } else {
            quote_spanned! { mixed_site =>
                let uninit = core::ptr::read(&this.uninit);
                uninit.assume_init()
            }
        };

        let slot_arg = pin_lifetime.as_ref().map(|pin_lifetime| {
            quote_spanned! { mixed_site =>
                slot: ::placid::pin::DropSlot<
                    #this_lifetime,
                    #pin_lifetime,
                    #ident<#(#ty_generics),*>,
                >,
            }
        });

        let slot_assign = pinned.then(|| {
            quote_spanned! { mixed_site => slot }
        });

        let (structural_trait, structural_ty, structural_func, structural_where) =
            if let Some(pin_lifetime) = &pin_lifetime {
                (
                    quote_spanned! { mixed_site => StructuralInitPin },
                    quote_spanned! { mixed_site => InitPin<#this_lifetime: #pin_lifetime> },
                    quote_spanned! { mixed_site => init_pin<#this_lifetime> },
                    quote_spanned! { mixed_site => where Self: #this_lifetime },
                )
            } else {
                (
                    quote_spanned! { mixed_site => StructuralInit },
                    quote_spanned! { mixed_site => Init },
                    quote_spanned! { mixed_site => init },
                    quote_spanned! { mixed_site => },
                )
            };

        quote_spanned! { mixed_site =>
            impl<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#generics,)*
            > #builder_ident<
                #this_lifetime,
                #(#pin_lifetime_q,)*
                #(#ty_generics,)*
                #typestate_ty_post
            > #where_clause {
                #[inline]
                #[doc(hidden)]
                pub fn build(self) -> #result_ty {
                    let mut this = ::core::mem::ManuallyDrop::new(self);
                    // SAFETY: All fields have been initialized.
                    unsafe { #assume_init }
                }
            }

            #[automatically_derived]
            impl<
                #init_lifetime,
                #(#bound_generics,)*
            > ::placid::init::#structural_trait<#init_lifetime> for #ident<
                #(#ty_generics,)*
            > #where_clause {
                type #structural_ty = #builder_ident<
                    #this_lifetime,
                    #(#pin_lifetime_q,)*
                    #(#ty_generics,)*
                    #typestate_ty_pre
                >
                #structural_where;

                #[inline]
                fn #structural_func(
                    uninit: ::placid::Uninit<
                        #this_lifetime,
                        #ident<#(#ty_generics),*>,
                    >,
                    #slot_arg
                ) -> #builder_ident<
                    #this_lifetime,
                    #(#pin_lifetime_q,)*
                    #(#ty_generics,)*
                    #typestate_ty_pre
                >
                #structural_where
                {
                    #builder_ident { uninit, #slot_assign }
                }
            }
        }
    });

    Ok(quote!(#(#builder)*))
}

pub fn init_pin(input: &DeriveInput) -> Result<TokenStream> {
    derive(input, true)
}

pub fn init(input: &DeriveInput) -> Result<TokenStream> {
    let mut tt = derive(input, false)?;
    tt.extend(derive(input, true)?);
    Ok(tt)
}
