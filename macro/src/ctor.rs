use std::mem;

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{Attribute, Expr, ExprCall, ExprPath, Meta, Type, visit_mut::VisitMut};

fn char_has_case(c: char) -> bool {
    let l = c.to_lowercase();
    let mut u = c.to_uppercase();
    for l in l {
        match u.next() {
            Some(u) if l != u => return true,
            _ => {}
        }
    }
    u.next().is_some()
}

fn is_camel_case(name: &str) -> bool {
    let name = name.trim_matches('_');
    if name.is_empty() {
        return true;
    }

    // start with a non-lowercase letter rather than non-uppercase
    // ones (some scripts don't have a concept of upper/lowercase)
    !name.chars().next().unwrap().is_lowercase()
        && !name.contains("__")
        && !name.chars().collect::<Vec<_>>().windows(2).any(|w| {
            match *w {
                [fst, snd] => {
                    // contains a capitalisable character followed by, or preceded by, an underscore
                    char_has_case(fst) && snd == '_' || char_has_case(snd) && fst == '_'
                }
                _ => false,
            }
        })
}

fn possible_struct_name(path: &ExprPath) -> bool {
    is_camel_case(&path.path.segments.last().unwrap().ident.to_string())
}

fn possible_struct_call(call: &ExprCall) -> bool {
    match &*call.func {
        Expr::Path(path) => possible_struct_name(path),
        _ => false,
    }
}

#[derive(Default)]
struct InitVisit {
    pinned: bool,
    err_ty: Option<Option<Type>>,
    err: Option<syn::Error>,
}

impl InitVisit {
    fn extend_err(&mut self, other: syn::Error) {
        if let Some(err) = &mut self.err {
            err.combine(other);
        } else {
            self.err = Some(other);
        }
    }

    fn scan_attribute(
        &mut self,
        attrs: &mut Vec<Attribute>,
        scan_pin: bool,
    ) -> (Option<Option<Type>>, Option<bool>) {
        let mut ret = None;
        let mut pinned = scan_pin.then_some(false);
        attrs.retain(|a| {
            if a.path().is_ident("err_into") {
                if ret.is_none() {
                    if matches!(a.meta, Meta::Path(_)) {
                        ret = Some(None);
                    } else {
                        match a.parse_args() {
                            Ok(ty) => ret = Some(Some(ty)),
                            Err(e) => self.extend_err(e),
                        }
                    }
                } else {
                    self.extend_err(syn::Error::new_spanned(a, "duplicate `err_into` attribute"));
                };
                false
            } else if scan_pin && self.pinned && a.path().is_ident("pin") {
                pinned = Some(true);
                if !matches!(a.meta, Meta::Path(_)) {
                    self.extend_err(syn::Error::new_spanned(
                        a,
                        "`pin` attribute does not take arguments",
                    ))
                }
                false
            } else {
                true
            }
        });
        (ret, pinned)
    }

    fn visit_inner_expr_mut(
        &mut self,
        expr: &mut Expr,
        (err_ty, pinned): (Option<Option<Type>>, Option<bool>),
    ) {
        let old_err = mem::replace(&mut self.err_ty, err_ty);
        let old_pinned = pinned.map(|pinned| mem::replace(&mut self.pinned, pinned));
        self.visit_expr_mut(expr);
        if let Some(old_pinned) = old_pinned {
            self.pinned = old_pinned;
        }
        self.err_ty = old_err;
    }

    fn visit_root_expr_mut(&mut self, expr: &mut Expr, scan_pin: bool) {
        let attrs = match match expr {
            Expr::Path(path) if possible_struct_name(path) => Some(&mut path.attrs),
            Expr::Call(call) if possible_struct_call(call) => Some(&mut call.attrs),
            Expr::Struct(ctor) => Some(&mut ctor.attrs),
            _ => None,
        } {
            Some(attrs) => self.scan_attribute(attrs, scan_pin),
            None => (None, None),
        };
        self.visit_inner_expr_mut(expr, attrs);
    }
}

impl VisitMut for InitVisit {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let span = Span::mixed_site();
        let (path, attrs, builder_segment) = match expr {
            Expr::Path(path) if possible_struct_name(path) => {
                (quote!(#path), mem::take(&mut path.attrs), Vec::new())
            }
            Expr::Call(call) if possible_struct_call(call) => {
                let path = &call.func;

                let mut builder_segment = Vec::new();
                for expr in &mut call.args {
                    self.visit_root_expr_mut(expr, true);

                    builder_segment.push(if self.err_ty.is_some() {
                        quote_spanned! { span =>
                            let builder = match builder.__next(#expr) {
                                Ok(v) => v,
                                Err(err) => return Err(err.map(Into::into)),
                            };
                        }
                    } else {
                        quote_spanned! { span =>
                            let builder = match builder.__next(#expr) {
                                Ok(v) => v,
                                Err(err) => return Err(err),
                            };
                        }
                    });
                }
                (quote!(#path), mem::take(&mut call.attrs), builder_segment)
            }
            Expr::Struct(ctor) => {
                let path = &ctor.path;

                let mut builder_segment = Vec::new();
                for field in &mut ctor.fields {
                    let member = &field.member;
                    let expr = &mut field.expr;

                    let attrs = self.scan_attribute(&mut field.attrs, true);
                    self.visit_inner_expr_mut(expr, attrs);

                    builder_segment.push(if self.err_ty.is_some() {
                        quote_spanned! { span =>
                            let builder = match builder.#member(#expr) {
                                Ok(v) => v,
                                Err(err) => return Err(err.map(Into::into)),
                            };
                        }
                    } else {
                        quote_spanned! { span =>
                            let builder = match builder.#member(#expr) {
                                Ok(v) => v,
                                Err(err) => return Err(err),
                            };
                        }
                    });
                }
                (quote!(#path), mem::take(&mut ctor.attrs), builder_segment)
            }
            _ => return,
        };

        let generics = if let Some(Some(err)) = &self.err_ty {
            quote_spanned! { span => ::<_, #err, _> }
        } else {
            quote_spanned! { span => ::<_, _, _> }
        };

        *expr = if self.pinned {
            syn::parse_quote_spanned! { span =>
                #(#attrs)*
                ::placid::init::try_raw_pin #generics(move |uninit, slot| {
                    use ::placid::init::StructuralInitPin;
                    let builder = #path::__builder_init_pin(uninit, slot);
                    #(#builder_segment)*
                    Ok(builder.build())
                })
            }
        } else {
            syn::parse_quote_spanned! { span =>
                #(#attrs)*
                ::placid::init::try_raw #generics(move |uninit| {
                    use ::placid::init::StructuralInit;
                    let builder = #path::__builder_init(uninit);
                    #(#builder_segment)*
                    Ok(builder.build())
                })
            }
        };
    }
}

pub fn init_pin(mut input: Expr) -> syn::Result<TokenStream> {
    let mut visitor = InitVisit {
        pinned: true,
        ..Default::default()
    };
    visitor.visit_root_expr_mut(&mut input, false);
    match visitor.err {
        None => Ok(quote!(::placid::__opaque_init_pin(#input))),
        Some(err) => Err(err),
    }
}

pub fn init(mut input: Expr) -> syn::Result<TokenStream> {
    let mut visitor = InitVisit {
        pinned: false,
        ..Default::default()
    };
    visitor.visit_root_expr_mut(&mut input, false);
    match visitor.err {
        None => Ok(quote!(::placid::__opaque_init(#input))),
        Some(err) => Err(err),
    }
}
