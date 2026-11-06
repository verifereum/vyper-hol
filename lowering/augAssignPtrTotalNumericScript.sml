Theory augAssignPtrTotalNumeric
Ancestors exprSimArith exprSimBinopFrag exprBopSimDefs exprLowering
  exprLoweringProps builtinProps builtinMath compileEnv list

Theorem unsafe_typed_numeric_witness:
  MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
  is_int_type ty /\ type_bits ty MOD 8 = 0 /\
  evaluate_type tenv ty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 ==>
  ?v. bop_result cx ty bop tys v1 v2 es = INL v /\ word_value v /\
      !x y sa sb op ss.
        compile_binop bop x y ty bl el sa = (op,sb) /\
        fresh_vars_wrt sa ss /\
        eval_operand x ss = SOME (val_to_w256 v1) /\
        eval_operand y ss = SOME (val_to_w256 v2) ==>
        ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
            eval_operand op t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  simp[] >> disch_then (qx_choose_then `i1` strip_assume_tac) >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  simp[] >> disch_then (qx_choose_then `i2` strip_assume_tac) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  qspecl_then [`cx`, `ty`, `bop`, `ty`] (mp_tac o SRULE []) bop_result_unsafe >>
  disch_then (qspecl_then [`es`, `i1`, `i2`] mp_tac) >>
  impl_tac >- fs[MEM] >> strip_tac >>
  qexists `v` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_binop_unsafe] >> strip_tac >>
  irule compile_unsafe_binop_correct >>
  goal_assum (drule_at (Pat `compile_unsafe_binop`)) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule step_unsafe_opcode >> asm_rewrite_tac[]
QED

(* Typed same-type words need not support ordering: the numerical witness
   interface for comparisons must retain expr_res_ok, as bop_result_compare does. *)
Theorem bool_lt_numeric_scope_probe:
  word_value_type (BaseT BoolT) /\
  evaluate_type tenv (BaseT BoolT) = SOME (BaseTV BoolT) /\
  value_has_type (BaseTV BoolT) (BoolV F) /\
  value_has_type (BaseTV BoolT) (BoolV T) /\
  bop_result cx (BaseT BoolT) Lt [] (BoolV F) (BoolV T) es =
    INR (Error (TypeError "binop"))
Proof
  EVAL_TAC
QED
