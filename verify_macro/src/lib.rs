use proc_macro::TokenStream;

#[proc_macro]
pub fn z3_verify(input: TokenStream) -> TokenStream {
    verify_macro_core::z3_verify(input.into()).unwrap().into()
}
