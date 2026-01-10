use proc_macro2::Span;
use quote::{quote, quote_spanned};
use syn::{
    Attribute, Expr, ExprCall, ExprPath, Type,
    visit_mut::{self, VisitMut},
};

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

fn scan_attribute(attrs: &mut Vec<Attribute>) -> Option<bool> {
    let mut ret = None;
    attrs.retain(|a| {
        if a.path().is_ident("unpin") {
            ret = Some(false);
            false
        } else if a.path().is_ident("pin") {
            ret = Some(true);
            false
        } else {
            true
        }
    });
    ret
}

struct InitVisit {
    should_replace: bool,
    pinned: bool,
    err: Option<Type>,
}

impl VisitMut for InitVisit {
    fn visit_expr_mut(&mut self, expr: &mut Expr) {
        let span = Span::mixed_site();
        let (path, builder_segment) = match expr {
            Expr::Path(path) if looks_like_tuple_struct_name(path) => {
                if let Some(v) = scan_attribute(&mut path.attrs) {
                    self.should_replace = v;
                }

                if !self.should_replace {
                    return visit_mut::visit_expr_mut(self, expr);
                }

                (quote!(#path), Vec::new())
            }
            Expr::Call(call) if looks_like_tuple_struct_call(call) => {
                if let Some(v) = scan_attribute(&mut call.attrs) {
                    self.should_replace = v;
                }

                if !self.should_replace {
                    // We must not visit call.func otherwise it'll be treated
                    // as unit struct.
                    for expr in &mut call.args {
                        self.visit_expr_mut(expr);
                    }
                    return;
                }

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
                (quote!(#path), builder_segment)
            }
            Expr::Struct(ctor) => {
                if let Some(v) = scan_attribute(&mut ctor.attrs) {
                    self.should_replace = v;
                }

                if !self.should_replace {
                    return visit_mut::visit_expr_mut(self, expr);
                }

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
                (quote!(#path), builder_segment)
            }
            _ => return visit_mut::visit_expr_mut(self, expr),
        };

        let generics = if let Some(ty) = &self.err {
            quote_spanned! { span => ::<_, #ty, _> }
        } else {
            quote_spanned! { span => }
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

pub struct Input {
    err: Option<syn::Type>,
    expr: Expr,
}

impl syn::parse::Parse for Input {
    fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        let mut err = None;
        for attr in input.call(syn::Attribute::parse_outer)? {
            if attr.path().is_ident("err") {
                if err.is_some() {
                    return Err(syn::Error::new_spanned(
                        attr,
                        "duplicate `err` attribute",
                    ));
                }
                err = Some(attr.parse_args()?);
            } else {
                return Err(syn::Error::new_spanned(
                    attr,
                    "unknown attribute, expected `err`",
                ));
            }
        }
        let expr = input.parse()?;
        Ok(Input { err, expr })
    }
}

pub fn init_pin(input: Input) -> syn::Result<Expr> {
    let mut visitor = InitVisit {
        should_replace: true,
        pinned: true,
        err: input.err,
    };
    let mut expr = input.expr;
    visitor.visit_expr_mut(&mut expr);
    Ok(expr)
}

pub fn init(input: Input) -> syn::Result<Expr> {
    let mut visitor = InitVisit {
        should_replace: true,
        pinned: false,
        err: input.err,
    };
    let mut expr = input.expr;
    visitor.visit_expr_mut(&mut expr);
    Ok(expr)
}
