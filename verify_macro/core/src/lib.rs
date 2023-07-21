use anyhow::Result;
use proc_macro2::TokenStream;
use quote::quote;

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

pub fn z3_verify(attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let _attr = syn::parse2::<syn::ExprBinary>(attr)?;
    let _item = syn::parse2::<syn::ItemFn>(item)?;
    let res = quote! {};
    Ok(res)
}

#[cfg(test)]
mod tests {
    use quote::{quote, ToTokens};

    // test verify attribute macro
    #[test]
    fn test_flatten_binaries() {
        let expr = quote! { a == b * c + d && a + b && (a + c || b + d) && !a };
        let expr = Box::new(syn::parse2::<syn::Expr>(expr).unwrap());
        let flattened = super::split_conditions(expr);
        for f in flattened {
            println!("{:?}", f.into_token_stream().to_string());
        }
        // let item = quote! {};
        // let res = super::z3_verify(attr.into(), item.into()).unwrap();
    }
}
