(* Consumer-facing source-success and dynamic-capture interface. *)
Theory exprSimSliceCapture
Ancestors
  exprSimSliceMemory exprSimSource exprSimProps exprLoweringProps
  exprReasonOperand exprOperandVar compileEnv loweringPosts vyperTypeExprResult
  vyperTypeExprSoundness vyperTypeInvariants vyperTyping

Theorem slice_source_dynamic_shape[local]:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_type src = BaseT bt /\ is_bytestring_type (BaseT bt) ==>
  expr_sim_inv cenv cx env ee /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
  ?cap bs. ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
    (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    32 + LENGTH bs <= val_footprint (BaseTV bt) v
Proof
  strip_tac >>
  `expr_body_pre cenv cx env src (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee /\ expr_result_typed env src (Value v)` by
    metis_tac[exprSimSourceTheory.expr_body_pre_eval] >>
  `env.type_defs = get_tenv cx` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  qpat_x_assum `expr_result_typed _ _ _` mp_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >>
  strip_tac >>
  Cases_on `bt` >> gvs[is_bytestring_type_def]
  >- (Cases_on `v` >> gvs[vyperValueTheory.evaluate_type_def,
        vyperTypingTheory.value_has_type_def, AllCaseEqs(), val_footprint_def]) >>
  Cases_on `b` >> gvs[is_bytestring_type_def,
    vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def, val_footprint_def]
QED

Theorem slice_source_dynamic_capture:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  lower_value compile_expr cenv (BaseT bt) src sa = (src_op,sm) /\
  compile_bytestring_src src_op sm = ((len_op,data),sc) /\
  local_ptrs_reserved cenv sm /\
  (!z. src_op = Var z ==> not_fresh_at sm z) /\ (!l. src_op <> Label l) ==>
  ?cap bs (p:bytes32) u.
    ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
     (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    expr_sim_inv cenv cx env ee /\
    run_inst_seq (emitted_insts sm sc) t = OK u /\
    stmt_state_rel ctx func cenv cx ee u /\
    eval_operand len_op u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (n2w (w2n p + 32)) /\
    expr_val_at cenv cx (BaseT bt) sa sc ee v src_op u /\
    eval_operand src_op u = SOME p /\
    w2n p + 32 < dimword (:256) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
    32 + LENGTH bs <= val_footprint (BaseTV bt) v /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx /\
    (!e sd ee' v' op' r.
      expr_post ctx func cenv cx e ee sc sd u ee' v' op' r ==>
      mem_bytes_at (w2n p + 32) (LENGTH bs) r.vs_memory = bs)
Proof
  strip_tac >> drule_all slice_source_dynamic_shape >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `cap` (qx_choose_then `bs`
        (CONJUNCTS_THEN assume_tac))))) >>
  `stmt_state_rel ctx func cenv cx ee t /\
   expr_val_rel cx (BaseT bt) v src_op t /\
   expr_val_at cenv cx (BaseT bt) sa sm ee v src_op t` by fs[expr_post_def] >>
  drule_all slice_dynamic_capture_continue >> strip_tac >>
  gvs[] >>
  (`stmt_state_rel ctx func cenv cx ee t'` by
     (qpat_x_assum `t' = t with vs_vars := _` SUBST1_TAC >>
      irule exprSimPropsTheory.stmt_state_rel_vars_frame >>
      simp[] >> rpt strip_tac >>
      fs[local_ptrs_reserved_def, venomStateTheory.lookup_var_def] >> metis_tac[]) >>
   `t'.vs_current_bb = t.vs_current_bb /\ t'.vs_inst_idx = t.vs_inst_idx` by
     (qpat_x_assum `t' = t with vs_vars := _` SUBST1_TAC >> simp[]) >>
   simp[] >> metis_tac[])
QED

(* The ordinary caller's source precondition discharges the existing
   nonlabel interface; freshness is a separate compiler invariant. *)
Theorem slice_source_operand_not_label:
  expr_body_pre cenv cx env src es /\
  lower_value compile_expr cenv ty src sa = (op,sb) ==>
  !l. op <> Label l
Proof
  strip_tac >> irule lower_compile_expr_not_label >>
  goal_assum (drule_at Any) >> qexists_tac `env` >>
  fs[exprSimHypsDefsTheory.expr_body_pre_def,
     exprSimHypsDefsTheory.expr_sim_inv_def]
QED

Theorem slice_source_dynamic_capture_reserved:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  lower_value compile_expr cenv (BaseT bt) src sa = (src_op,sm) /\
  compile_bytestring_src src_op sm = ((len_op,data),sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm ==>
  ?cap bs (p:bytes32) u.
    ((bt = BytesT (Dynamic cap) /\ v = BytesV bs) \/
     (?str. bt = StringT cap /\ v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    expr_sim_inv cenv cx env ee /\
    run_inst_seq (emitted_insts sm sc) t = OK u /\
    stmt_state_rel ctx func cenv cx ee u /\
    eval_operand len_op u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (n2w (w2n p + 32)) /\
    expr_val_at cenv cx (BaseT bt) sa sc ee v src_op u /\
    eval_operand src_op u = SOME p /\
    w2n p + 32 < dimword (:256) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\
    32 + LENGTH bs <= val_footprint (BaseTV bt) v /\
    u.vs_current_bb = t.vs_current_bb /\ u.vs_inst_idx = t.vs_inst_idx /\
    (!e sd ee' v' op' r.
      expr_post ctx func cenv cx e ee sc sd u ee' v' op' r ==>
      mem_bytes_at (w2n p + 32) (LENGTH bs) r.vs_memory = bs)
Proof
  strip_tac >>
  `!z. src_op = Var z ==> not_fresh_at sm z` by
    metis_tac[compile_lower_value_var] >>
  `!l. src_op <> Label l` by
    (drule_all slice_source_operand_not_label >> simp[]) >>
  drule_all slice_source_dynamic_capture >> simp[]
QED
