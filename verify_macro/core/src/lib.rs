use anyhow::{Context, Result};
use indexmap::IndexSet;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{quote, ToTokens};
use syn::{BinOp, Expr, ExprArray, Lit, UnOp};

// Splits the constraints into a vector of unary, binary or parenthe expressions
fn split_constraints(expr: &Expr) -> Vec<&Expr> {
    let bin_ex = match expr {
        Expr::Binary(b) => b,
        Expr::Unary(_) | Expr::Paren(_) => return vec![expr],
        _ => return vec![],
    };

    match bin_ex.op {
        BinOp::And(_) | BinOp::Or(_) => {
            let mut left = split_constraints(&bin_ex.left);
            let right = split_constraints(&bin_ex.right);
            left.extend(right);
            left
        }
        _ => {
            vec![expr]
        }
    }
}

fn get_ints_to_declare(consts: &IndexSet<Ident>, expr: &Expr) -> IndexSet<Expr> {
    match expr {
        Expr::Binary(b) => {
            let mut left_unique = get_ints_to_declare(consts, &b.left);
            let right_unique = get_ints_to_declare(consts, &b.right);
            left_unique.extend(right_unique);
            left_unique
        }
        Expr::Paren(p) => get_ints_to_declare(consts, &p.expr),
        Expr::Lit(l) => {
            if let Lit::Int(_) = &l.lit {
                [expr.clone()].into()
            } else {
                [].into()
            }
        }
        Expr::Unary(u) => get_ints_to_declare(consts, &u.expr),
        Expr::Path(p) => {
            let p = p.to_token_stream().to_string();
            let ident = Ident::new(&p, Span::call_site());
            if consts.contains(&ident) {
                [].into()
            } else {
                [expr.clone()].into()
            }
        }
        _ => [].into(),
    }
}

fn declare_const(input_idx: usize, ident: &Ident) -> TokenStream {
    let name = format!("input_{input_idx}");
    let ident = Ident::new(&format!("__{ident}"), Span::call_site());
    quote! {
        let #ident = z3::ast::Int::new_const(&ctx_z3, #name);
    }
}

fn declare_int(exp: &Expr) -> TokenStream {
    let name = exp.to_token_stream().to_string();
    let ident = Ident::new(&format!("__{name}"), Span::call_site());
    quote! {
        let #ident = z3::ast::Int::from_i64(&ctx_z3, #exp);
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

fn declare_constraint(name: &str, expr: &Expr) -> TokenStream {
    fn create_constraint(expr: &Expr) -> TokenStream {
        match expr {
            Expr::Binary(b) => {
                let lhs = if expr_is_path_or_literal(&b.left) {
                    let l = format!("__{}", b.left.to_token_stream());
                    let l = Ident::new(&l, Span::call_site());
                    quote! { #l }
                } else {
                    create_constraint(&b.left)
                };

                let rhs = if expr_is_path_or_literal(&b.right) {
                    let r = format!("__{}", b.right.to_token_stream());
                    let r = Ident::new(&r, Span::call_site());
                    quote! { #r }
                } else {
                    create_constraint(&b.right)
                };

                let z3_op = bin_op_to_z3(b.op);
                quote! {
                    (#lhs).#z3_op(&#rhs)
                }
            }
            Expr::Paren(p) => create_constraint(&p.expr),
            Expr::Unary(u) => {
                let expr = if expr_is_path_or_literal(&u.expr) {
                    let e = format!("__{}", u.expr.to_token_stream());
                    let e = Ident::new(&e, Span::call_site());
                    quote! { #e }
                } else {
                    create_constraint(&u.expr)
                };

                let z3_op = un_op_to_z3(u.op);
                quote! {
                    (#expr).#z3_op()
                }
            }
            _ => panic!("invalid"),
        }
    }

    let cond = create_constraint(expr);
    let id = Ident::new(name, Span::call_site());
    quote! {
        let #id = #cond;
    }
}

fn split_stream_into_consts_and_constraints(stream: &TokenStream) -> Result<(ExprArray, Expr)> {
    let stream = stream.to_string();
    let (consts, constraints) = stream.split_once(';').context("splitting proc macro failed")?;
    let consts = consts.parse::<TokenStream>().map_err(|_| anyhow::anyhow!("invalid consts"))?;
    let consts = syn::parse2(consts)?;
    let constraints =
        constraints.parse::<TokenStream>().map_err(|_| anyhow::anyhow!("invalid constraints"))?;
    let constraints = syn::parse2(constraints)?;
    Ok((consts, constraints))
}

fn path_expr_to_ident(expr: &Expr) -> Result<Ident> {
    if let Expr::Path(p) = expr {
        let p = p.to_token_stream().to_string();
        let ident = Ident::new(&p, Span::call_site());
        Ok(ident)
    } else {
        anyhow::bail!("invalid declarations")
    }
}

fn const_array_to_set(consts: &ExprArray) -> Result<IndexSet<Ident>> {
    let mut res = IndexSet::new();
    for v in consts.elems.iter() {
        let id = path_expr_to_ident(v)?;
        res.insert(id);
    }
    Ok(res)
}

fn create_const_declarations(consts: &ExprArray) -> Result<TokenStream> {
    let mut res = vec![];
    for (i, v) in consts.elems.iter().enumerate() {
        let id = path_expr_to_ident(v)?;
        let d = declare_const(i, &id);
        res.push(d);
    }

    Ok(quote! {
        let vec = vec!#consts;
        #(#res)*
    })
}

fn create_conditions(consts_set: &IndexSet<Ident>, constraints: &Expr) -> TokenStream {
    let ints = get_ints_to_declare(consts_set, constraints);
    let int_declarations = ints.iter().map(declare_int);
    let constraints = split_constraints(constraints);

    let mut condition_idents = vec![];
    let mut conditions = vec![];

    for (i, c) in constraints.iter().enumerate() {
        let name = format!("__condition_{i}");
        let ident = Ident::new(&name, Span::call_site());
        condition_idents.push(ident);
        conditions.push(declare_constraint(&name, c));
    }

    let goal = quote! {
        let goal = z3::ast::Bool::and(&ctx_z3, &[#(&#condition_idents),*]);
    };

    quote! {
        #(#int_declarations)*
        #(#conditions)*
        #goal
    }
}

pub fn z3_verify(expr: &TokenStream) -> Result<TokenStream> {
    let (consts, constraints) = split_stream_into_consts_and_constraints(expr)?;
    let consts_set = const_array_to_set(&consts)?;
    let const_declarations = create_const_declarations(&consts)?;
    let conditions = create_conditions(&consts_set, &constraints);
    let res = quote! {
        let cfg = z3::Config::new();
        let ctx_z3 = z3::Context::new(&cfg);
        let solver = z3::Solver::new(&ctx_z3);
        #const_declarations
        #conditions
        z3_formally_verify(ctx, &ctx_z3, &solver, &goal, &vec);
    };
    Ok(res)
}

#[cfg(test)]
mod tests {
    use proc_macro2::{Ident, Span};
    use quote::{quote, ToTokens};
    use syn::Expr;

    use crate::z3_verify;

    #[test]
    fn test_split_conditions_1() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = syn::parse2(expr).unwrap();
        let flattened = super::split_constraints(&expr);
        assert_eq!(flattened.len(), 4);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a == b * c + d");
        assert_eq!(flattened[1].to_token_stream().to_string(), "a + b");
        assert_eq!(flattened[2].to_token_stream().to_string(), "(a + c || b + d)");
        assert_eq!(flattened[3].to_token_stream().to_string(), "! a");
    }

    #[test]
    fn test_split_conditions_2() {
        let expr = quote! { a == b };
        let expr = syn::parse2(expr).unwrap();
        let flattened = super::split_constraints(&expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a == b");
    }

    #[test]
    fn test_split_conditions_3() {
        let expr = quote! { return };
        let expr = syn::parse2(expr).unwrap();
        let flattened = super::split_constraints(&expr);
        assert_eq!(flattened.len(), 0);
    }

    #[test]
    fn test_split_conditions_4() {
        let expr = quote! { (((a + b))) };
        let expr = syn::parse2(expr).unwrap();
        let flattened = super::split_constraints(&expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "(((a + b)))");
    }

    #[test]
    fn test_split_conditions_5() {
        let expr = quote! { a > 1 };
        let expr = syn::parse2(expr).unwrap();
        let flattened = super::split_constraints(&expr);
        assert_eq!(flattened.len(), 1);
        assert_eq!(flattened[0].to_token_stream().to_string(), "a > 1");
    }

    #[test]
    fn test_create_declarations() {
        let expr = quote! { [a, b, c, d] };
        let expr = syn::parse2(expr).unwrap();
        let vars = super::create_const_declarations(&expr).unwrap();
        let expected = "let vec = vec ! [a , b , c , d] ; let __a = z3 :: ast :: Int :: new_const (& ctx_z3 , \"input_0\") ; let __b = z3 :: ast :: Int :: new_const (& ctx_z3 , \"input_1\") ; let __c = z3 :: ast :: Int :: new_const (& ctx_z3 , \"input_2\") ; let __d = z3 :: ast :: Int :: new_const (& ctx_z3 , \"input_3\") ;";
        assert_eq!(vars.to_string(), expected);
    }

    #[test]
    fn test_declare_consts_1() {
        let ident = syn::Ident::new("a", Span::call_site());
        let res = super::declare_const(0, &ident);
        assert_eq!(
            res.to_string(),
            "let __a = z3 :: ast :: Int :: new_const (& ctx_z3 , \"input_0\") ;"
        );
    }

    #[test]
    fn test_get_ints_to_declare_1() {
        let expr = quote! { 1 };
        let expr = syn::parse2(expr).unwrap();
        let res = super::get_ints_to_declare(&[].into(), &expr);
        assert_eq!(res.len(), 1);
        assert!(res.contains(&expr));
    }

    #[test]
    fn test_unique_literal_ints_2() {
        let expr = quote! { 1 + 2 + 3 + a + b + ((((c + d)))) };
        let expr = syn::parse2(expr).unwrap();
        let a = Ident::new("a", Span::call_site());
        let b = Ident::new("b", Span::call_site());
        let c = Ident::new("c", Span::call_site());
        let res = super::get_ints_to_declare(&[a, b, c].into(), &expr);
        assert_eq!(res.len(), 4);

        let one = syn::parse2::<Expr>(quote! { 1 }).unwrap();
        let two = syn::parse2::<Expr>(quote! { 2 }).unwrap();
        let three = syn::parse2::<Expr>(quote! { 3 }).unwrap();
        let d = syn::parse2::<Expr>(quote! { d }).unwrap();
        assert!(res.contains(&one));
        assert!(res.contains(&two));
        assert!(res.contains(&three));
        assert!(res.contains(&d));
    }

    #[test]
    fn test_declare_constraint_1() {
        let expr = quote! { a == b };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(condition.to_string(), "let one = (__a) . eq (& __b) ;");
    }

    #[test]
    fn test_declare_constraint_2() {
        let expr = quote! { a + b + c == 3 };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . add (& __b)) . add (& __c)) . eq (& __3) ;"
        )
    }

    #[test]
    fn test_declare_constraint_3() {
        let expr = quote! { a + b + c == 3 + d };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . add (& __b)) . add (& __c)) . eq (& (__3) . add (& __d)) ;"
        )
    }

    #[test]
    fn test_declare_constraint_4() {
        let expr = quote! { a + b + c > 3 + d };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . add (& __b)) . add (& __c)) . gt (& (__3) . add (& __d)) ;"
        )
    }

    #[test]
    fn test_declare_constraint_5() {
        let expr = quote! { (a - b) + c > 4 * (d / 6) };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        println!("{}", condition.to_string());
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . sub (& __b)) . add (& __c)) . gt (& (__4) . mul (& (__d) . div (& __6))) ;"
        )
    }

    #[test]
    fn test_declare_constraint_6() {
        let expr = quote! { ((a - b) + c > 4 * (d / 6)) };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        println!("{}", condition.to_string());
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . sub (& __b)) . add (& __c)) . gt (& (__4) . mul (& (__d) . div (& __6))) ;"
        )
    }

    #[test]
    fn test_declare_constraint_7() {
        let expr = quote! { a };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        assert_eq!(constraints.len(), 0);
    }

    #[test]
    fn test_declare_constraint_8() {
        let expr = quote! { !a };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(condition.to_string(), "let one = (__a) . not () ;");
    }

    #[test]
    fn test_declare_constraint_9() {
        let expr = quote! { !!a };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(condition.to_string(), "let one = ((__a) . not ()) . not () ;");
    }

    #[test]
    fn test_declare_constraint_10() {
        let expr = quote! { !(a + b > 0) };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(
            condition.to_string(),
            "let one = (((__a) . add (& __b)) . gt (& __0)) . not () ;"
        );
    }

    #[test]
    fn test_declare_constraint_11() {
        let expr = quote! { !!!!((a - b) + c > 4 * (d / 6)) };
        let expr = syn::parse2(expr).unwrap();
        let constraints = super::split_constraints(&expr);
        let condition = super::declare_constraint("one", constraints[0]);
        assert_eq!(condition.to_string(), "let one = (((((((__a) . sub (& __b)) . add (& __c)) . gt (& (__4) . mul (& (__d) . div (& __6)))) . not ()) . not ()) . not ()) . not () ;");
    }

    #[test]
    fn test_create_conditions_1() {
        let expr = quote! { a == b };
        let expr = syn::parse2(expr).unwrap();
        let a_id = Ident::new("a", Span::call_site());
        let b_id = Ident::new("b", Span::call_site());
        let set = [a_id, b_id].into();
        let conditions = super::create_conditions(&set, &expr);
        let expected = "let __condition_0 = (__a) . eq (& __b) ; let goal = z3 :: ast :: Bool :: and (& ctx_z3 , & [& __condition_0]) ;";
        assert_eq!(conditions.to_string(), expected);
    }

    #[test]
    fn test_create_conditions_2() {
        let expr = quote! { a == b && a > 0 && b < 3 };
        let expr = syn::parse2(expr).unwrap();
        let a_id = Ident::new("a", Span::call_site());
        let b_id = Ident::new("b", Span::call_site());
        let set = [a_id, b_id].into();
        let conditions = super::create_conditions(&set, &expr);
        let expected = "let __0 = z3 :: ast :: Int :: from_i64 (& ctx_z3 , 0) ; let __3 = z3 :: ast :: Int :: from_i64 (& ctx_z3 , 3) ; let __condition_0 = (__a) . eq (& __b) ; let __condition_1 = (__a) . gt (& __0) ; let __condition_2 = (__b) . lt (& __3) ; let goal = z3 :: ast :: Bool :: and (& ctx_z3 , & [& __condition_0 , & __condition_1 , & __condition_2]) ;";
        assert_eq!(conditions.to_string(), expected);
    }

    #[test]
    fn test_create_conditions_3() {
        let expr = quote! { a > test_int };
        let expr = syn::parse2(expr).unwrap();
        let a_id = Ident::new("a", Span::call_site());
        let set = [a_id].into();
        let conditions = super::create_conditions(&set, &expr);
        let expected = "let __test_int = z3 :: ast :: Int :: from_i64 (& ctx_z3 , test_int) ; let __condition_0 = (__a) . gt (& __test_int) ; let goal = z3 :: ast :: Bool :: and (& ctx_z3 , & [& __condition_0]) ;";
        assert_eq!(conditions.to_string(), expected);
    }

    #[test]
    fn test_z3_verify_1() {
        let expr = quote! { [a]; a >= 0 };
        let r = z3_verify(&expr).unwrap();
        println!("{}", r);
    }
}
