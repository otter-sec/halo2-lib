#![allow(dead_code)]
use std::collections::HashSet;

use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{BinOp, Expr, ExprBinary, ItemFn, Lit, LitInt, UnOp};

// Splits the constraints into a vector of unary, binary or parenthe expressions
fn split_conditions(expr: Expr) -> Vec<Expr> {
    let expr = match expr {
        Expr::Binary(b) => b,
        Expr::Unary(_) => return vec![expr],
        Expr::Paren(_) => return vec![expr],
        _ => return vec![],
    };

    match expr.op {
        BinOp::And(_) | BinOp::Or(_) => {
            let mut left = split_conditions(*expr.left);
            let right = split_conditions(*expr.right);
            left.extend(right);
            left
        }
        _ => {
            vec![Expr::Binary(expr)]
        }
    }
}

fn get_unique_variable(expr: Expr) -> HashSet<Ident> {
    match expr {
        Expr::Binary(b) => {
            let mut left_unique = get_unique_variable(*b.left);
            let right_unique = get_unique_variable(*b.right);
            left_unique.extend(right_unique);
            left_unique
        }
        Expr::Paren(p) => get_unique_variable(*p.expr),
        Expr::Path(p) => {
            let p = p.to_token_stream().to_string();
            let i = Ident::new(&p, Span::call_site());
            [i].into()
        }
        Expr::Unary(u) => get_unique_variable(*u.expr),
        _ => [].into(),
    }
}

fn get_unique_int_literals(expr: Expr) -> HashSet<LitInt> {
    match expr {
        Expr::Binary(b) => {
            let mut left_unique = get_unique_int_literals(*b.left);
            let right_unique = get_unique_int_literals(*b.right);
            left_unique.extend(right_unique);
            left_unique
        }
        Expr::Paren(p) => get_unique_int_literals(*p.expr),
        Expr::Lit(l) => {
            if let Lit::Int(lit) = l.lit {
                [lit].into()
            } else {
                [].into()
            }
        }
        Expr::Unary(u) => get_unique_int_literals(*u.expr),
        _ => [].into(),
    }
}

fn declare_consts(ident: Ident) -> TokenStream {
    let name = format!("__{}", ident);
    let ident = Ident::new(&name, Span::call_site());
    quote! {
        let #ident = z3::ast::Int::new_const(&ctx, #name);
    }
}

fn declare_int_literals(lit: LitInt) -> TokenStream {
    let name = format!("__{}", lit);
    let ident = Ident::new(&name, Span::call_site());
    quote! {
        let #ident = z3::ast::Int::from_i64(&ctx, #lit);
    }
}

fn bin_op_to_z3(op: BinOp) -> TokenStream {
    let s = match op {
        BinOp::Add(_) => "add",
        BinOp::Sub(_) => "sub",
        BinOp::Mul(_) => "mul",
        BinOp::Div(_) => "div",
        BinOp::Rem(_) => "rem",
        BinOp::Eq(_) => "eq",
        BinOp::Lt(_) => "lt",
        BinOp::Le(_) => "le",
        BinOp::Ne(_) => "ne",
        BinOp::Ge(_) => "ge",
        BinOp::Gt(_) => "gt",
        _ => panic!("invalid"),
    };
    s.parse().unwrap()
}

fn un_op_to_z3(op: UnOp) -> TokenStream {
    let s = match op {
        UnOp::Not(_) => "not",
        UnOp::Neg(_) => "neg",
        _ => panic!("invalid"),
    };
    s.parse().unwrap()
}

pub fn z3_verify(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let _attr = syn::parse2::<ExprBinary>(attr)?;
    let _item = syn::parse2::<ItemFn>(item)?;
    let res = quote! {};
    Ok(res)
}

#[cfg(test)]
mod tests {
    use proc_macro2::Span;
    use quote::{quote, ToTokens};
    use syn::LitInt;

    #[test]
    fn test_split_conditions_1() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::split_conditions(expr);
        assert_eq!(flattened.len(), 4);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a == b * c + d");
        assert_eq!(flattened[1].to_token_stream().to_string(), "a + b");
        assert_eq!(flattened[2].to_token_stream().to_string(), "(a + c || b + d)");
        assert_eq!(flattened[3].to_token_stream().to_string(), "! a");
    }

    #[test]
    fn test_split_conditions_2() {
        let expr = quote! { a == b };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::split_conditions(expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a == b");
    }

    #[test]
    fn test_split_conditions_3() {
        let expr = quote! { return };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::split_conditions(expr);
        assert_eq!(flattened.len(), 0);
    }

    #[test]
    fn test_split_conditions_4() {
        let expr = quote! { (((a + b))) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::split_conditions(expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "(((a + b)))");
    }

    #[test]
    fn test_split_conditions_5() {
        let expr = quote! { a > 1 };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::split_conditions(expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a > 1");
    }

    #[test]
    fn test_unique_variables_1() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
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
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let vars = super::get_unique_variable(expr);
        assert_eq!(vars.len(), 0);
    }

    #[test]
    fn test_unique_variables_3() {
        let expr = quote! { (((a + b))) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let vars = super::get_unique_variable(expr);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&syn::Ident::new("a", Span::call_site())));
        assert!(vars.contains(&syn::Ident::new("b", Span::call_site())));
    }

    #[test]
    fn test_unique_variables_4() {
        let expr = quote! { a > 1 };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let vars = super::get_unique_variable(expr);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&syn::Ident::new("a", Span::call_site())));
    }

    #[test]
    fn test_declare_consts_1() {
        let ident = syn::Ident::new("a", Span::call_site());
        let res = super::declare_consts(ident);
        assert_eq!(res.to_string(), "let __a = z3 :: ast :: Int :: new_const (& ctx , \"__a\") ;");
    }

    #[test]
    fn test_unique_literal_ints_1() {
        let expr = quote! { 1 };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let res = super::get_unique_int_literals(expr);
        assert_eq!(res.len(), 1);
        assert!(res.contains(&LitInt::new("1", Span::call_site())));
    }

    #[test]
    fn test_unique_literal_ints_2() {
        let expr = quote! { 1 + 2 + 3 + a + b + ((((c + d)))) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let res = super::get_unique_int_literals(expr);
        assert_eq!(res.len(), 3);
        assert!(res.contains(&LitInt::new("1", Span::call_site())));
        assert!(res.contains(&LitInt::new("2", Span::call_site())));
        assert!(res.contains(&LitInt::new("3", Span::call_site())));
    }

    #[test]
    fn test_declare_int_literals() {
        let int = LitInt::new("1", Span::call_site());
        let res = super::declare_int_literals(int);
        assert_eq!(res.to_string(), "let __1 = z3 :: ast :: Int :: from_i64 (& ctx , 1) ;");
    }
}
