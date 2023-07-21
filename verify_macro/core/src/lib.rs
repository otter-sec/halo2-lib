use anyhow::Result;
use proc_macro2::TokenStream;
use quote::quote;

pub fn z3_verify(_attr: TokenStream, item: TokenStream) -> Result<TokenStream> {
    let _item = syn::parse2::<syn::ItemFn>(item).unwrap();
    let res = quote! {};
    Ok(res)
}
