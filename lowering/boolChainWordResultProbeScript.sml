Theory boolChainWordResultProbe
Ancestors
  exprLowering compileEnv emitHelper loweringStateRelDefs ASCIInumbers

(* The literal-safety conjunct expands safe_operand_def without importing
   exprSafeOperand. The remaining conjunct models the singleton chain suffix. *)
Theorem bool_chain_word_result_boundary:
  r = FST (fresh_var sa) /\
  a = SND (emit_inst ASSIGN [Lit w] [r] u) /\
  b = SND (emit_inst JMP [Label l] [] a) /\
  z = SND (new_block l b) ==>
  is_word_type (BaseT BoolT) /\
  lower_value (\ce' t e' s. (StackValue t (Lit w),u)) ce (BaseT BoolT) e s =
    (Lit w,u) /\
  ((!x. Lit w = Var x ==> not_fresh_at u x) /\ (!lbl. Lit w <> Label lbl)) /\
  (not_fresh_at z r <=> sa.cs_next_var < u.cs_next_var)
Proof
  rpt strip_tac >>
  gvs[is_word_type_def, lower_value_def, unwrap_value_def, comp_bind_def,
      comp_return_def, not_fresh_at_def, fresh_var_def, emit_inst_def,
      comp_ignore_bind_def, fresh_id_def, emit_def, new_block_def, toString_inj] >>
  metis_tac[arithmeticTheory.NOT_LESS_EQUAL]
QED
