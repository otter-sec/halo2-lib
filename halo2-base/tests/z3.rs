use halo2_base::gates::{
    builder::{GateThreadBuilder, RangeCircuitBuilder},
    range::{RangeChip, RangeInstructions},
};
use halo2_base::halo2_proofs::{dev::MockProver, halo2curves::bn256::Fr};
use halo2_base::utils::{z3_formally_verify, BigPrimeField};
use halo2_base::Context;
use verify_macro::z3_verify;
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
    z3_verify!([a]; a >= 0 && a < max_range);

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

fn z3_check_less_than<F: BigPrimeField>(
    ctx: &mut Context<F>,
    lookup_bits: usize,
    inputs: [F; 2],
    range_bits: usize,
    _lt_bits: usize,
) {
    let [a, b]: [_; 2] = ctx.assign_witnesses(inputs).try_into().unwrap();
    let chip = RangeChip::default(lookup_bits);

    std::env::set_var("LOOKUP_BITS", lookup_bits.to_string());

    // First range check a
    chip.check_less_than(ctx, a, b, range_bits);
    let max_range = 2 << range_bits;
    z3_verify!([a, b]; a < 0 || a >= max_range || b < 0 || b >= max_range  ||  a < b);
}

#[test]
fn test_z3_check_less_than() {
    let k = 11;
    let inputs = [100, 101].map(Fr::from);
    let mut builder = GateThreadBuilder::mock();
    z3_check_less_than(builder.main(0), 3, inputs, 8, 8);

    // auto-tune circuit
    builder.config(k, Some(9));
    // create circuit
    let circuit = RangeCircuitBuilder::mock(builder);

    MockProver::run(k as u32, &circuit, vec![]).unwrap().assert_satisfied();
}
