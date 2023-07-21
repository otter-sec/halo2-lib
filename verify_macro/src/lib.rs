use proc_macro::TokenStream;

#[proc_macro_attribute]
pub fn z3_verify(args: TokenStream, input: TokenStream) -> TokenStream {
    verify_macro_core::z3_verify(args.into(), input.into()).unwrap().into()
}
