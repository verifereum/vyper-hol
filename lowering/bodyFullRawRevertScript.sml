(*
 * raw_revert over the finite-horizon joint judgment: the data operand and
 * the REVERT tail share one origin/memory/pointer witness.
 *
 * The shadow-compile premise is the lower_value form of the gas-shadow
 * compile spine (gas_shadow_compiles_lower_value with
 * gas_shadow_compile_expr), which this base doesn't carry yet;
 * body_raw_revert_case_full discharges it once it does.
 *
 * TOP-LEVEL:
 *   raw_revert_expr_full_ok
 *)
Theory bodyFullRawRevert
Ancestors
  bodyFullRawRevertCompiledTail bodyFullRawRevertValue
  bodyFullRawRevertPackaging bodyFullPreds bodySimFull
  gasShadowState gasShadow exprLowering vyperAST list

val _ = Parse.hide "body";

Theorem raw_revert_expr_full_ok:
  !cx ann es dflt.
    (!cenv ty e.
       gas_shadow_compiles (lower_value compile_expr cenv ty e)
         (lower_value compile_expr cenv ty (gas_shadow_expr e))) /\
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ann RawRevert es dflt)
Proof
  mp_tac raw_revert_body_full_from_value >>
  (impl_tac >-
    (mp_tac raw_revert_value_full_from_tail >>
     (impl_tac >-
       (rpt gen_tac >> strip_tac >>
        drule_all raw_revert_compiled_tail_joint >> simp[])) >>
     simp[])) >>
  simp[]
QED
