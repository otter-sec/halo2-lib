use std::collections::HashSet;

use anyhow::Result;
use proc_macro2::{TokenStream, Span, Ident};
use quote::{quote, ToTokens};

#[allow(dead_code)]
// Splits the constraints into a vector of unary, binary or parenthe expressions
fn split_conditions(expr: Box<syn::Expr>) -> Vec<syn::Expr> {
    let expr = match *expr {
        syn::Expr::Binary(b) => b,
        syn::Expr::Unary(ref _u) => return vec![*expr],
        syn::Expr::Paren(ref _p) => return vec![*expr],
        _ => return vec![],
    };

    match expr.op {
        syn::BinOp::And(_) | syn::BinOp::Or(_) => {
            let mut left = split_conditions(expr.left);
            let right = split_conditions(expr.right);
            left.extend(right);
            left
        }
        _ => {
            vec![syn::Expr::Binary(expr)]
        }
    }
}

#[allow(dead_code)]
fn get_unique_variable(expr: Box<syn::Expr>) -> HashSet<Ident> {
    match *expr {
        syn::Expr::Binary(b) => {
            let mut left_unique = get_unique_variable(b.left);
            let right_unique = get_unique_variable(b.right);
            left_unique.extend(right_unique);
            left_unique
        },
        syn::Expr::Paren(p) => get_unique_variable(p.expr),
        syn::Expr::Path(p) => {
            let p = p.to_token_stream().to_string();
            let i = syn::Ident::new(&p, Span::call_site());
            [i].into()
        }
        syn::Expr::Unary(u) => get_unique_variable(u.expr),
        _ => return [].into()
    }
}

#[allow(dead_code)]
fn declare_consts(ident: Ident) -> TokenStream {
    quote! {
        let #ident = z3::ast::Int::new_const(&ctx, "#ident");
    }
}

pub fn z3_verify(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let _attr = syn::parse2::<syn::ExprBinary>(attr)?;
    let _item = syn::parse2::<syn::ItemFn>(item)?;
    let res = quote! {};
    Ok(res)
}

#[cfg(test)]
mod tests {
    use proc_macro2::Span;
    use quote::{quote, ToTokens};

    #[test]
    fn test_flatten_binaries_1() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let flattened = super::split_conditions(expr.clone());
        assert_eq!(flattened.len(), 4);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a == b * c + d");
        assert_eq!(flattened[1].to_token_stream().to_string(), "a + b");
        assert_eq!(flattened[2].to_token_stream().to_string(), "(a + c || b + d)");
        assert_eq!(flattened[3].to_token_stream().to_string(), "! a");
    }

    #[test]
    fn test_flatten_binaries_2() {
        let expr = quote! { a == b };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let flattened = super::split_conditions(expr.clone());
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a == b");
    }

    #[test]
    fn test_flatten_binaries_3() {
        let expr = quote! { return };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let flattened = super::split_conditions(expr.clone());
        assert_eq!(flattened.len(), 0);
    }

    #[test]
    fn test_flatten_binaries_4() {
        let expr = quote! { (((a + b))) };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let flattened = super::split_conditions(expr.clone());
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "(((a + b)))");
    }

    #[test]
    fn test_unique_variables_1() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let vars = super::get_unique_variable(expr);
        assert_eq!(vars.len(), 4);
        assert!(vars.contains(&syn::Ident::new("a", Span::call_site())));
        assert!(vars.contains(&syn::Ident::new("b", Span::call_site())));
        assert!(vars.contains(&syn::Ident::new("c", Span::call_site())));
        assert!(vars.contains(&syn::Ident::new("d", Span::call_site())));
    }

    #[test]
    fn test_unique_variables_2() {
        let expr = quote! { return };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let vars = super::get_unique_variable(expr);
        assert_eq!(vars.len(), 0);
    }

    #[test]
    fn test_unique_variables_3() {
        let expr = quote! { (((a + b))) };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let vars = super::get_unique_variable(expr);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&syn::Ident::new("a", Span::call_site())));
        assert!(vars.contains(&syn::Ident::new("b", Span::call_site())));
    }
}
