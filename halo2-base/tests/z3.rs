extern crate halo2_base;
extern crate num_bigint;
extern crate num_traits;

use halo2_base::gates::{
    builder::{GateThreadBuilder, RangeCircuitBuilder},
    range::{RangeChip, RangeInstructions},
};
use halo2_base::halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use halo2_base::utils::{fe_to_biguint, z3_formally_verify, BigPrimeField};
use halo2_base::Context;
use z3::ast::Ast;
use verify_macro::z3_verify;
use num_traits::ToPrimitive;
use halo2_base::gates::flex_gate::GateInstructions;
// use z3::{ast::{Bool, Int}, Config, Solver};

// Example of how to formally verify a circuit
fn z3_range_test<F: BigPrimeField>(
    ctx: &mut Context<F>,
    lookup_bits: usize,
    inputs: [F; 2],
    range_bits: usize,
    _lt_bits: usize,
) {
    let [a, _]: [_; 2] = ctx.assign_witnesses(inputs).try_into().unwrap();
    let chip = RangeChip::default(lookup_bits);

    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

    // First range check a
    chip.range_check(ctx, a, range_bits);
    let max_range = 2 << range_bits;
    // This macro is the equivalent of all the commented out code below it
    z3_verify!([a]; [a >= 0, a < max_range]; "and");

    // setting up a z3 solver and input the circuit and a to the solver.
    // let vec = vec![&a];
    // let cfg = z3::Config::new();
    // let ctx_z3 = z3::Context::new(&cfg);
    // let solver = z3::Solver::new(&ctx_z3);

    // // specifications defined by users, input_0 is a (next input would be input_1 and so on)
    // // a >= 0
    // let a_ge_0 =
    //     z3::ast::Int::new_const(&ctx_z3, "input_0").ge(&z3::ast::Int::from_u64(&ctx_z3, 0));
    // a < 2**range_bits
    // let a_lt_2numbits = z3::ast::Int::new_const(&ctx_z3, "input_0")
    //     .lt(&z3::ast::Int::from_u64(&ctx_z3, 2 << range_bits));
    // //  0 <= a < 2**range_bits
    // let goal = z3::ast::Bool::and(&ctx_z3, &[&a_ge_0, &a_lt_2numbits]);

    // z3_formally_verify(ctx, &ctx_z3, &solver, &goal, &vec);
}

#[test]
fn test_z3_range_check() {
    let k = 11;
    let inputs = [100, 0].map(Fr::from);
    let mut builder = GateThreadBuilder::mock();
    z3_range_test(builder.main(0), 3, inputs, 8, 8);

    // auto-tune circuit
    builder.config(k, Some(9));
    // create circuit
    let circuit = RangeCircuitBuilder::mock(builder);

    MockProver::run(k as u32, &circuit, vec![]).unwrap().assert_satisfied();
}

#[test]
fn test_z3_div_mod() {
    let k = 11;
    let inputs = [100, 10].map(Fr::from);

    let mut builder = GateThreadBuilder::mock();

    let ctx = builder.main(0);

    let [a]: [_; 1] = ctx.assign_witnesses([inputs[0]]).try_into().unwrap();
    let chip = RangeChip::default(3);
    let lookup_bits = 3;
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());
    let (div, rem) = chip.div_mod(ctx, a, fe_to_biguint(&inputs[1]), 8);
    println!("div : {:?}", div.value());
    println!("rem : {:?}", rem.value());
    let b_cell = ctx.get(2);
    z3_verify!([a, b_cell, div, rem]; [a == b_cell * div + rem]; "and");
}

#[test]
fn test_z3_div_mod_var() {
    let k = 11;
    let inputs = [100, 10].map(Fr::from);

    let mut builder = GateThreadBuilder::mock();

    let ctx = builder.main(0);

    let [a, b]: [_; 2] = ctx.assign_witnesses(inputs).try_into().unwrap();
    let chip = RangeChip::default(3);
    let lookup_bits = 3;
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());
    let (div, rem) = chip.div_mod_var(ctx, a, b, 8, 8);
    println!("div : {:?}", div.value());
    println!("rem : {:?}", rem.value());
    z3_verify!([a, b, div, rem]; [a == b* div + rem]; "and");
}

#[test]
fn test_z3_get_last_bit() {
    let k = 11;
    let inputs = [100, 10].map(Fr::from);

    let mut builder = GateThreadBuilder::mock();

    let ctx = builder.main(0);

    let [a, b]: [_; 2] = ctx.assign_witnesses(inputs).try_into().unwrap();
    let chip = RangeChip::default(3);
    let lookup_bits = 3;
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());
    let (bit) = chip.get_last_bit(ctx, a,  8);
    z3_verify!([bit]; [bit == 0, bit == 1]  ; "or");
}

#[test]
fn test_z3_assert_bit() {
    let k = 11;
    let inputs = [100, 10].map(Fr::from);

    let mut builder = GateThreadBuilder::mock();

    let ctx = builder.main(0);

    let [a, b]: [_; 2] = ctx.assign_witnesses(inputs).try_into().unwrap();
    let chip = RangeChip::default(3);
    let lookup_bits = 3;
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());
    chip.gate().assert_bit(ctx,a);
    z3_verify!([a]; [a == 0, a == 1]  ; "or");
}

#[test]
fn test_z3_check_less_than() {
    let k = 11;
    let inputs = [100, 10].map(Fr::from);

    let mut builder = GateThreadBuilder::mock();

    let ctx = builder.main(0);

    let [a, b]: [_; 2] = ctx.assign_witnesses(inputs).try_into().unwrap();
    let chip = RangeChip::default(3);
    let lookup_bits = 3;
    let range_bits = 8;
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());
    chip.check_less_than(ctx, a, b, range_bits);
    let max_range = 2 << range_bits;
    z3_verify!([a, b]; [a < 0, a >= max_range, b < 0, b >= max_range, a < b]; "or");
}

#[test]
fn test_z3_check_less_than_safe() {
    let k = 11;
    let inputs = [100, 10].map(Fr::from);

    let mut builder = GateThreadBuilder::mock();

    let ctx = builder.main(0);

    let [a]: [_; 1] = ctx.assign_witnesses([inputs[0]]).try_into().unwrap();
    let chip = RangeChip::default(3);
    let lookup_bits = 3;
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());
    let b = fe_to_biguint(&inputs[1]).to_u64().unwrap();
    let b_i64 = fe_to_biguint(&inputs[1]).to_i64().unwrap();
    chip.check_less_than_safe(ctx, a, b);
    z3_verify!([a]; [a < b_i64]; "and");
}

#[test]
fn test_z3_check_less_than_const() {
    let k = 11;
    let inputs = [100, 10].map(Fr::from);

    let mut builder = GateThreadBuilder::mock();

    let ctx = builder.main(0);

    let [a, b]: [_; 2] = ctx.assign_witnesses(inputs).try_into().unwrap();
    let chip = RangeChip::default(3);
    let lookup_bits = 3;
    let range_bits = 8;
    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

    chip.check_less_than_z3const(ctx, a, b, range_bits);

    let z3_constraints = &ctx.z3_constraints;

    let max_range = 2 << range_bits;
    z3_verify!([a, b]; [a < 0, a >= max_range, b < 0, b >= max_range, a < b]; "or");
}
