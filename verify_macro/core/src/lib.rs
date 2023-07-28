#![allow(dead_code)]
use std::collections::HashSet;

use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{BinOp, Expr, ItemFn, Lit, LitInt, UnOp};

// Splits the constraints into a vector of unary, binary or parenthe expressions
fn get_constraints(expr: &Expr) -> Vec<&Expr> {
    let bin_ex = match expr {
        Expr::Binary(b) => b,
        Expr::Unary(_) => return vec![expr],
        Expr::Paren(_) => return vec![expr],
        _ => return vec![],
    };

    match bin_ex.op {
        BinOp::And(_) | BinOp::Or(_) => {
            let mut left = get_constraints(&bin_ex.left);
            let right = get_constraints(&bin_ex.right);
            left.extend(right);
            left
        }
        _ => {
            vec![expr]
        }
    }
}

fn get_unique_variables(expr: &Expr) -> HashSet<Ident> {
    match expr {
        Expr::Binary(b) => {
            let mut left_unique = get_unique_variables(&b.left);
            let right_unique = get_unique_variables(&b.right);
            left_unique.extend(right_unique);
            left_unique
        }
        Expr::Paren(p) => get_unique_variables(&p.expr),
        Expr::Path(p) => {
            let p = p.to_token_stream().to_string();
            let i = Ident::new(&p, Span::call_site());
            [i].into()
        }
        Expr::Unary(u) => get_unique_variables(&u.expr),
        _ => [].into(),
    }
}

fn get_unique_int_literals(expr: &Expr) -> HashSet<LitInt> {
    match expr {
        Expr::Binary(b) => {
            let mut left_unique = get_unique_int_literals(&b.left);
            let right_unique = get_unique_int_literals(&b.right);
            left_unique.extend(right_unique);
            left_unique
        }
        Expr::Paren(p) => get_unique_int_literals(&p.expr),
        Expr::Lit(l) => {
            if let Lit::Int(lit) = &l.lit {
                [lit.clone()].into()
            } else {
                [].into()
            }
        }
        Expr::Unary(u) => get_unique_int_literals(&u.expr),
        _ => [].into(),
    }
}

fn declare_const(input_idx: u8, ident: &Ident) -> TokenStream {
    let name = format!("input_{input_idx}");
    let ident = Ident::new(&format!("__{ident}"), Span::call_site());
    quote! {
        let #ident = z3::ast::Int::new_const(&ctx, #name);
    }
}

fn declare_int_literal(lit: &LitInt) -> TokenStream {
    let name = format!("__{lit}");
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

fn expr_is_path_or_literal(expr: &Expr) -> bool {
    matches!(expr, Expr::Path(_) | Expr::Lit(_))
}

fn declare_condition(name: String, expr: &Expr) -> TokenStream {
    fn create_condition(expr: &Expr) -> TokenStream {
        match expr {
            Expr::Binary(b) => {
                let lhs = if expr_is_path_or_literal(&b.left) {
                    let l = format!("__{}", b.left.to_token_stream().to_string());
                    let l = Ident::new(&l, Span::call_site());
                    quote! { #l }
                } else {
                    create_condition(&b.left)
                };

                let rhs = if expr_is_path_or_literal(&b.right) {
                    let r = format!("__{}", b.right.to_token_stream().to_string());
                    let r = Ident::new(&r, Span::call_site());
                    quote! { #r }
                } else {
                    create_condition(&b.right)
                };

                let z3_op = bin_op_to_z3(b.op);
                quote! {
                    (#lhs).#z3_op(#rhs)
                }
            }
            Expr::Paren(p) => create_condition(&p.expr),
            Expr::Unary(u) => {
                let expr = if expr_is_path_or_literal(&u.expr) {
                    let e = format!("__{}", u.expr.to_token_stream().to_string());
                    let e = Ident::new(&e, Span::call_site());
                    quote! { #e }
                } else {
                    create_condition(&u.expr)
                };

                let z3_op = un_op_to_z3(u.op);
                quote! {
                    (#expr).#z3_op()
                }
            }
            _ => panic!("invalid"),
        }
    }

    let cond = create_condition(expr);
    let id = Ident::new(&name, Span::call_site());
    quote! {
        let #id = #cond;
    }
}

pub fn z3_verify(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let attr = syn::parse2::<Expr>(attr)?;
    let vars = get_unique_variables(&attr);
    let ints = get_unique_int_literals(&attr);
    let const_declarations = vars.iter().enumerate().map(|(i, v)| declare_const(i as u8, v));
    let int_declarations = ints.iter().map(declare_int_literal);
    let constraints = get_constraints(&attr);
    let conditions = constraints.iter().enumerate().map(|(i, c)| {
        let name = format!("__condition_{}", i);
        declare_condition(name, c)
    });

    let item = syn::parse2::<ItemFn>(item)?;
    let sig = item.sig;
    let body = item.block.stmts;

    let res = quote! {
        #sig {
            #(#const_declarations)*
            #(#int_declarations)*
            #(#conditions)*
            #(#body)*
        }
    };
    Ok(res)
}

#[cfg(test)]
mod tests {
    use proc_macro2::Span;
    use quote::{quote, ToTokens};
    use syn::LitInt;

    use crate::z3_verify;

    #[test]
    fn test_split_conditions_1() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::get_constraints(&expr);
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
        let flattened = super::get_constraints(&expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a == b");
    }

    #[test]
    fn test_split_conditions_3() {
        let expr = quote! { return };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::get_constraints(&expr);
        assert_eq!(flattened.len(), 0);
    }

    #[test]
    fn test_split_conditions_4() {
        let expr = quote! { (((a + b))) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::get_constraints(&expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "(((a + b)))");
    }

    #[test]
    fn test_split_conditions_5() {
        let expr = quote! { a > 1 };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let flattened = super::get_constraints(&expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a > 1");
    }

    #[test]
    fn test_unique_variables_1() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let vars = super::get_unique_variables(&expr);
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
        let vars = super::get_unique_variables(&expr);
        assert_eq!(vars.len(), 0);
    }

    #[test]
    fn test_unique_variables_3() {
        let expr = quote! { (((a + b))) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let vars = super::get_unique_variables(&expr);
        assert_eq!(vars.len(), 2);
        assert!(vars.contains(&syn::Ident::new("a", Span::call_site())));
        assert!(vars.contains(&syn::Ident::new("b", Span::call_site())));
    }

    #[test]
    fn test_unique_variables_4() {
        let expr = quote! { a > 1 };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let vars = super::get_unique_variables(&expr);
        assert_eq!(vars.len(), 1);
        assert!(vars.contains(&syn::Ident::new("a", Span::call_site())));
    }

    #[test]
    fn test_declare_consts_1() {
        let ident = syn::Ident::new("a", Span::call_site());
        let res = super::declare_const(0, &ident);
        assert_eq!(
            res.to_string(),
            "let __a = z3 :: ast :: Int :: new_const (& ctx , \"input_0\") ;"
        );
    }

    #[test]
    fn test_unique_literal_ints_1() {
        let expr = quote! { 1 };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let res = super::get_unique_int_literals(&expr);
        assert_eq!(res.len(), 1);
        assert!(res.contains(&LitInt::new("1", Span::call_site())));
    }

    #[test]
    fn test_unique_literal_ints_2() {
        let expr = quote! { 1 + 2 + 3 + a + b + ((((c + d)))) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let res = super::get_unique_int_literals(&expr);
        assert_eq!(res.len(), 3);
        assert!(res.contains(&LitInt::new("1", Span::call_site())));
        assert!(res.contains(&LitInt::new("2", Span::call_site())));
        assert!(res.contains(&LitInt::new("3", Span::call_site())));
    }

    #[test]
    fn test_declare_int_literals() {
        let int = LitInt::new("1", Span::call_site());
        let res = super::declare_int_literal(&int);
        assert_eq!(res.to_string(), "let __1 = z3 :: ast :: Int :: from_i64 (& ctx , 1) ;");
    }

    #[test]
    fn test_create_conditions_1() {
        let expr = quote! { a == b };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(condition.to_string(), "let one = (__a) . eq (__b) ;");
    }

    #[test]
    fn test_create_conditions_2() {
        let expr = quote! { a + b + c == 3 };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . add (__b)) . add (__c)) . eq (__3) ;"
        )
    }

    #[test]
    fn test_create_conditions_3() {
        let expr = quote! { a + b + c == 3 + d };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . add (__b)) . add (__c)) . eq ((__3) . add (__d)) ;"
        )
    }

    #[test]
    fn test_create_conditions_4() {
        let expr = quote! { a + b + c > 3 + d };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . add (__b)) . add (__c)) . gt ((__3) . add (__d)) ;"
        )
    }

    #[test]
    fn test_create_conditions_5() {
        let expr = quote! { (a - b) + c > 4 * (d / 6) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        println!("{}", condition.to_string());
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . sub (__b)) . add (__c)) . gt ((__4) . mul ((__d) . div (__6))) ;"
        )
    }

    #[test]
    fn test_create_conditions_6() {
        let expr = quote! { ((a - b) + c > 4 * (d / 6)) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        println!("{}", condition.to_string());
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . sub (__b)) . add (__c)) . gt ((__4) . mul ((__d) . div (__6))) ;"
        )
    }

    #[test]
    fn test_create_conditions_7() {
        let expr = quote! { a };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        assert_eq!(constraints.len(), 0);
    }

    #[test]
    fn test_create_conditions_8() {
        let expr = quote! { !a };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(condition.to_string(), "let one = (__a) . not () ;");
    }

    #[test]
    fn test_create_conditions_9() {
        let expr = quote! { !!a };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(condition.to_string(), "let one = ((__a) . not ()) . not () ;");
    }

    #[test]
    fn test_create_conditions_10() {
        let expr = quote! { !(a + b > 0) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(condition.to_string(), "let one = (((__a) . add (__b)) . gt (__0)) . not () ;");
    }

    #[test]
    fn test_create_conditions_11() {
        let expr = quote! { !!!!((a - b) + c > 4 * (d / 6)) };
        let expr = syn::parse2::<syn::Expr>(expr).unwrap();
        let constraints = super::get_constraints(&expr);
        let condition = super::declare_condition("one".to_string(), constraints[0]);
        assert_eq!(condition.to_string(), "let one = (((((((__a) . sub (__b)) . add (__c)) . gt ((__4) . mul ((__d) . div (__6)))) . not ()) . not ()) . not ()) . not () ;");
    }

    #[test]
    fn test_z3_verify() {
        let attr = quote! { a + b + c < 1 && a + b == 0 };
        let item = quote! {
            fn foo() -> i32 {
                println!("hello world");
            }
        };
        let r = z3_verify(attr, item).unwrap();
        println!("{}", r);
    }
}
