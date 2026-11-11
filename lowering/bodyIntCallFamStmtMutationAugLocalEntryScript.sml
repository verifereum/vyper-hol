(* Direct-local augmented assignment: source readiness and readonly load. *)
Theory bodyIntCallFamStmtMutationAugLocalEntry
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationLoad stmtSimAugAssign
  bodyExprPreFacts bodySim vyperTypeSystem vyperTyping vyperTypeInvariants
  supportedStmtTraverse supportedExprs supportedStmts vyperTypeCallGraph gasContext
  vyperTypeCallStackSoundness loweringSlice
  exprSimHypsDefs emitHelperProps venomState venomInst compileEnv finite_map

Theorem intcall_augassign_local_typing:
  type_stmt env ret (AugAssign ty (NameTarget id) bop e) = SOME env' ==>
  FLOOKUP env.var_types id = SOME ty /\
  well_typed_expr env e /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e)
Proof
  strip_tac >>
  gvs[type_stmt_def,well_typed_target_def,well_typed_expr_def,
      DISJ_IMP_THM,AllCaseEqs()] >>
  Cases_on `FLOOKUP env.var_types id` >>
  Cases_on `FLOOKUP env.var_assignable id` >> gvs[] >>
  rename1 `FLOOKUP env.var_assignable id = SOME asg` >>
  Cases_on `asg` >> gvs[]
QED

Theorem intcall_mload_cont:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  emit_op MLOAD [pop] sa = (op,sb) /\ fn_has_code sa sb fp.jc_func /\
  eval_operand pop s = SOME w /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      eval_operand op u = SOME (mload (w2n w) s) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >> irule intcall_emit_readonly_cont >> simp[] >>
  qexistsl [`[pop]`,`MLOAD`] >> simp[is_terminator_def] >>
  gen_tac >> irule step_MLOAD >> simp[]
QED

Theorem intcall_augassign_local_rhs_pre:
  intcall_frame_ok fp /\ body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  intcall_joint_res fp ce env es sa s /\
  type_stmt env ret (AugAssign ty (NameTarget id) bop e) = SOME env' /\
  supported_stmt fp.jc_tops bindings (AugAssign ty (NameTarget id) bop e) /\
  stmt_exprs_ok ce (AugAssign ty (NameTarget id) bop e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target fp.jc_tops) /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) ==>
  expr_body_pre ce fp.jc_cx env e es
Proof
  strip_tac >>
  drule intcall_augassign_local_typing >> strip_tac >>
  `supported_expr fp.jc_tops e` by fs[supported_stmt_def] >>
  drule supported_expr_body_calls >> strip_tac >>
  irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre)) >>
  simp[] >>
  fs[intcall_joint_res_def,intcall_expr_res_def,stmt_exprs_ok_def,
     supported_stmt_expr_exists_def,intcall_frame_ok_def,body_inv_def,
     gasContextTheory.cx_tops_def,call_evaluation_safe_def] >>
  metis_tac[]
QED

Theorem intcall_augassign_local_load:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es sa s /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
  lookup_scopes id es.scopes = SOME entry /\ word_value entry.value /\
  emit_op MLOAD [Var p] sa = (op,sb) /\ fn_has_code sa sb fp.jc_func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
      eval_operand op u = SOME (val_to_w256 entry.value) /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      intcall_expr_cont fp ce env es sa s es sb u
Proof
  strip_tac >> irule intcall_emit_readonly_cont >> simp[] >>
  qexistsl [`[Var p]`,`MLOAD`] >> simp[is_terminator_def] >>
  gen_tac >> irule step_name_word >>
  fs[intcall_expr_res_def] >> metis_tac[]
QED
