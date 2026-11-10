(* Storage-place continuation after a counted target traversal. *)
Theory augAssignPlaceEndpointStorage
Ancestors
  augAssignPlaceEndpointMemory augAssignPlaceLoadedStorage
  augAssignPlaceStorageContinuation augAssignPlaceLoadContinuation
  augAssignPlaceSourceMemory bodyAugAssignOther bodyMemoryDefs
  exprSimHyps vyperInterpreter exprSimMemDefs stmtSimAugAssignPlace bodySim

Theorem aug_place_storage_endpoint:
  body_inv tops ctx cenv cx /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  EVERY (supported_pure_expr tops) (target_indices bt) /\
  (!s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx bt s = (INL p,s1) /\ read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  target_post ctx func cenv cx es sa sp s0 mid
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r t /\
  (!tail. eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (StoragePlace tr slot tv),mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  emit_op (if tr then TLOAD else SLOAD) [FST r] sp = (cur,sl) /\
  lower_value compile_expr cenv ty e sl = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [FST r;result] s3 = ((),sf) /\
  fn_has_code sp sl func /\ fn_has_code sl s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sp /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\
  (!z. not_fresh_at sa z ==> not_fresh_at sp z) /\
  (!z. not_fresh_at sp z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sp.cs_current_bb /\ t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  (!res ee v. res = INL () /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 res ee v /\
    alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next ==> Q res ee v) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (read_place cx (StoragePlace tr slot tv)) (\old.
      bind (place_type_value cx (StoragePlace tr slot tv)) (\ptv.
      bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop old rhs)) (write_place cx (StoragePlace tr slot tv)))))) (mid,t) Q
    (\res ff rr. !tail. stmt_exit RetQ (ff with gas_obs := tail) res rr)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule aug_place_typing >> strip_tac >>
  `is_word_type ty` by metis_tac[exprSimSourceTheory.word_value_type_word] >>
  `type_bits ty MOD 8 = 0` by
    metis_tac[vyperTypeSystemTheory.assignable_type_well_formed,
              stmtSimAugAssignTheory.well_formed_type_bits] >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (assume_tac o SRULE [] o Q.SPEC `mid.gas_obs`) >>
  drule_at (Pat `target_post`) aug_place_storage_loaded >>
  disch_then (drule_at (Pat `eval_target_place`)) >>
  disch_then (drule_at (Pat `emit_op`)) >> simp[] >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >>
  disch_then (drule_at (Pat `expr_body_pre`)) >> simp[] >> strip_tac >>
  `expr_body_pre cenv cx env e mid` by
    (irule stmtSimAugAssignPlaceMemoryTheory.aug_place_rhs_pre_target_gas_obs >>
     goal_assum (drule_at (Pat `eval_target_place`)) >> simp[]) >>
  `expr_sim_mem ctx func cenv cx ty e mid` by
    (`body_expr_mem_ok cx e` by metis_tac[] >>
     fs[bodyMemoryPredsTheory.body_expr_mem_ok_def] >> metis_tac[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `~cx.txn.is_static` by fs[exprLoweringPropsTheory.stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  `storage_place_region cx (StoragePlace tr slot tv)` by
    metis_tac[vyperStoragePlaceProvenanceTheory.eval_target_place_region] >>
  `~block_is_terminated sf` by
    (Cases_on `tr` >>
     irule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
  `!l. cur <> Label l /\ FST r <> Label l` by
    (drule_all stmtSimAugAssignPlaceTheory.aug_place_target_ptr_not_label >>
     strip_tac >> gvs[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sl z` by metis_tac[] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  irule aug_place_reads_suffix >> simp[] >>
  qexists_tac `\res ee v. res = INL () /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 res ee v /\
    alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next` >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_path`)) >> simp[] >>
  irule aug_place_loaded_storage_suffix >> simp[] >> conj_tac
  >- (goal_assum (drule_at (Pat `lower_value`)) >>
      goal_assum (drule_at (Pat `compile_binop`)) >> simp[] >> metis_tac[]) >>
  goal_assum (drule_at (Pat `type_stmt`)) >>
  goal_assum (drule_at (Pat `eval_target_place`)) >> simp[]
QED
