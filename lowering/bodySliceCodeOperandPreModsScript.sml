(* The two forced word operands of a Slice whose source is account code. *)
Theory bodySliceCodeOperandPreMods
Ancestors
  exprBodyPreProps exprSimSliceSource exprSimHypsDefs exprLowering
  allocLimits supportedExprTraverse vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperInterpreter vyperAST list

Theorem slice_code_operand_pre_mods:
  code_slice_source (Slice n) args = SOME (ct,addr) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) args) es ==>
  ?start len. args = [Builtin ct (Acc Code) [addr];start;len] /\
    expr_type start = BaseT (UintT 256) /\
    expr_type len = BaseT (UintT 256) /\
    (!e mid. MEM e [start;len] /\ expr_sim_inv_mods mods cenv cx env mid ==>
             expr_body_pre_mods mods cenv cx env e mid)
Proof
  simp[code_slice_source_SOME] >> strip_tac >> gvs[] >>
  rename1 `expr_body_pre_mods _ _ _ _ (Builtin _ _ [_;start;len]) _` >>
  `expr_type start = BaseT (UintT 256) /\
   expr_type len = BaseT (UintT 256)` by
    (drule expr_body_pre_mods_well_typed >>
     disch_then (mp_tac o MATCH_MP slice_typed_args) >> simp[]) >>
  simp[] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, is_extcode_def, extcode_addr_expr_def,
       int_calls_expr_def, EVERY_APPEND, supported_expr_exists_def,
       expr_has_evm_run_thm, DISJ_IMP_THM, FORALL_AND_THM] >>
  strip_tac >>
  drule_then strip_assume_tac call_evaluation_safe_append_right >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED
