use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned};
use syn::{Attribute, Expr, ExprCall, ExprPath, Result, Type, visit_mut::VisitMut};

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

fn looks_like_tuple_struct_name(path: &ExprPath) -> bool {
    is_camel_case(&path.path.segments.last().unwrap().ident.to_string())
}

fn looks_like_tuple_struct_call(call: &ExprCall) -> bool {
    match &*call.func {
        Expr::Path(path) => looks_like_tuple_struct_name(path),
        _ => false,
    }
}

fn scan_attribute(attrs: &mut Vec<Attribute>) -> Result<Option<Type>> {
    let mut ret = None;
    attrs.retain(|a| {
        if a.path().is_ident("err") {
            ret = if ret.is_none() {
                Some(a.parse_args())
            } else {
                Some(Err(syn::Error::new_spanned(a, "duplicate `err` attribute")))
            };
            false
        } else {
            true
        }
    });
    ret.transpose()
}

struct InitVisit {
    pinned: bool,
    err: Option<syn::Error>,
}

impl VisitMut for InitVisit {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let span = Span::mixed_site();
        let (path, err, builder_segment) = match expr {
            Expr::Path(path) if looks_like_tuple_struct_name(path) => {
                let err = scan_attribute(&mut path.attrs).unwrap_or_else(|e| {
                    self.err = Some(e);
                    None
                });

                (quote!(#path), err, Vec::new())
            }
            Expr::Call(call) if looks_like_tuple_struct_call(call) => {
                let err = scan_attribute(&mut call.attrs).unwrap_or_else(|e| {
                    self.err = Some(e);
                    None
                });

                let path = &call.func;

                let mut builder_segment = Vec::new();
                for expr in &mut call.args {
                    self.visit_expr_mut(expr);
                    builder_segment.push(if self.err.is_some() {
                        quote_spanned! { span =>
                            let builder = builder.next(#expr)?;
                        }
                    } else {
                        quote_spanned! { span =>
                            let builder = match builder.next(#expr) {
                                Ok(v) => v,
                                Err(err) => return Err(err),
                            };
                        }
                    });
                }
                (quote!(#path), err, builder_segment)
            }
            Expr::Struct(ctor) => {
                let err = scan_attribute(&mut ctor.attrs).unwrap_or_else(|e| {
                    self.err = Some(e);
                    None
                });

                let path = &ctor.path;

                let mut builder_segment = Vec::new();
                for field in &mut ctor.fields {
                    let member = &field.member;
                    let expr = &mut field.expr;
                    self.visit_expr_mut(expr);
                    builder_segment.push(if self.err.is_some() {
                        quote_spanned! { span =>
                            let builder = builder.#member(#expr)?;
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
                (quote!(#path), err, builder_segment)
            }
            _ => return,
        };

        let generics = if let Some(err) = err {
            quote_spanned! { span => ::<#path, #err, _> }
        } else {
            quote_spanned! { span => ::<#path, _, _> }
        };

        *expr = if self.pinned {
            syn::parse_quote_spanned! { span =>
                ::placid::init::try_raw_pin #generics(move |uninit, slot| {
                    use ::placid::init::StructuralInitPin;
                    let builder = <#path as StructuralInitPin>::init_pin(uninit, slot);
                    #(#builder_segment)*
                    Ok(builder.build())
                })
            }
        } else {
            syn::parse_quote_spanned! { span =>
                ::placid::init::try_raw #generics(move |uninit| {
                    use ::placid::init::StructuralInit;
                    let builder = <#path as StructuralInit>::init(uninit);
                    #(#builder_segment)*
                    Ok(builder.build())
                })
            }
        };
    }
}

pub fn init_pin(mut input: Expr) -> syn::Result<TokenStream> {
    let mut visitor = InitVisit { pinned: true, err: None };
    visitor.visit_expr_mut(&mut input);
    Ok(quote!(#input))
}

pub fn init(mut input: Expr) -> syn::Result<TokenStream> {
    let mut visitor = InitVisit { pinned: false, err: None };
    visitor.visit_expr_mut(&mut input);
    Ok(quote!(#input))
}
