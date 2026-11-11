(*
 * Fuel bounds (fuel_ok) for the expression-lowering helpers.
 *
 * TOP-LEVEL: (filled in at the end)
 *)

Theory fragFuelExprHelpers
Ancestors
  fragFuel fragFuelContextBase fragFuelContext compileEnv emitHelper context
  venomInst exprLowering
Libs
  fragFuelLib

val ft = fn ths =>
  fuel_auto (fuel_ok_emit_op :: fuel_ok_emit_void_any :: fuel_ok_emit_inst_any ::
             ths) >> rw[is_terminator_def];

Theorem fuel_ok_compile_clamp:
  !v ty Wv E. fuel_ok Wv {} E (compile_clamp v ty)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_clamp_def] >>
  Cases_on `type_bounds ty` >> simp_tac std_ss [LET_THM, pairTheory.UNCURRY_DEF] >>
  match_mp_tac fuel_ok_if >> conj_tac >> strip_tac >> ft []
QED

Theorem fuel_ok_clamp_and_return:
  !v ty Wv E. fuel_ok Wv {} E (clamp_and_return v ty)
Proof
  rpt gen_tac >> simp_tac std_ss [clamp_and_return_def] >>
  ft [fuel_ok_compile_clamp]
QED

Theorem fuel_ok_compile_clamp_basetype:
  !v ty Wv E. fuel_ok Wv {} E (compile_clamp_basetype v ty)
Proof
  ho_match_mp_tac compile_clamp_basetype_ind >> rpt strip_tac >>
  simp_tac std_ss [compile_clamp_basetype_def] >>
  ft [fuel_ok_clamp_and_return]
QED

Theorem fuel_ok_arith_basic:
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_add x y ty)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_sub x y ty)) /\
  (!x y res s bits Wv E.
     fuel_ok Wv {} E (compile_mul_overflow_check x y res s bits)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_mul x y ty)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_div x y ty)) /\
  (!x y d ty Wv E. fuel_ok Wv {} E (compile_safe_decimal_div x y d ty)) /\
  (!x y ty Wv E. fuel_ok Wv {} E (compile_safe_mod x y ty)) /\
  (!r ty Wv E. fuel_ok Wv {} E (wrap_truncate r ty))
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp_tac std_ss [compile_safe_add_def, compile_safe_sub_def,
    compile_mul_overflow_check_def, compile_safe_mul_def, compile_safe_div_def,
    compile_safe_decimal_div_def, compile_safe_mod_def, wrap_truncate_def,
    pairTheory.UNCURRY_DEF] >>
  ft [fuel_ok_clamp_and_return, fuel_ok_compile_clamp]
QED

Theorem fuel_ok_compile_compare:
  !op x y ty Wv E. fuel_ok Wv {} E (compile_compare op x y ty)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_compare_def, LET_THM] >>
  Cases_on `op` >> simp_tac (srw_ss()) [] >> ft []
QED

Theorem fuel_ok_compile_safe_pow:
  !x y ty bl el Wv E. fuel_ok Wv {} E (compile_safe_pow x y ty bl el)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_safe_pow_def] >>
  Cases_on `bl` >> Cases_on `el` >> simp_tac std_ss [optionTheory.option_case_def] >>
  ft [fuel_ok_compile_clamp]
QED
