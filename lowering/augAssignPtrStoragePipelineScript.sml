(* Compiler assembly for an arbitrary pure storage-place target. *)
Theory augAssignPtrStoragePipeline
Ancestors
  augAssignPtrStorageContinuation augAssignPtrStoragePlaceCertificates
  augAssignPtrStorageCommon augAssignPtrSource augAssignPtrRhsFrame
  bodyPtrPreds bodyPtrDefs exprSimHypsDefs exprSimSource exprSimProps
  exprSimDefs exprReasonOperand exprOperandVar exprSimHyps exprSimUnwrap
  vyperTypeBuiltins vyperTypeValues vyperTypeSystem vyperTypeStatePreservation
  vyperTyping vyperState vyperInterpreter exprBopSimProps
  loweringPosts compileEnv emitHelperProps exprLoweringProps
  codegenRel stmtSimProps stmtSimDefs stmtSimAugAssign
  fragExec loweringSlice gasSummary gasContext stmtFragPtr
  fragGasPathPtr gasSummaryComposePtr ptrDiscipline

Theorem augassign_storage_place_pipeline_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  (!gs. eval_target_place cx tgt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tvt),es with gas_obs := gs)) /\
  read_storage_slot cx tr slot tvt es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  well_formed_type env.type_defs ty /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  (!w st. storage_dead cx tr (update_storage slot w st) = storage_dead cx tr st) /\
  lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (op,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] s3 = ((),sb) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sb func /\
  cs_extends sa s1 /\ cs_extends s1 s2 /\ sa.cs_next_var <= s1.cs_next_var /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  local_ptrs_reserved cenv s1 /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
  gas_admissible (eval_stmt cx (AugAssign ty tgt bop e)) (stmt_res_ok lctx) es /\
  gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 H tm (OK t) /\
  stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es H tm t /\
  ghost_kept cenv es sa G0 tn0 s0 H tm /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts /\
  eval_operand cur t = SOME (val_to_w256 v) /\ eval_operand dst t = SOME slot /\
  (!l. cur <> Label l /\ dst <> Label l) /\
  op_prov H cur = NONE /\ op_taint tm cur = {} /\ op_taint tm dst = {} /\
  (!z. cur = Var z ==> not_fresh_at s1 z) /\
  (!z. dst = Var z ==> not_fresh_at s1 z) /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s0) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_stmt cx (AugAssign ty tgt bop e)) (es,s0,G0,tn0)
    (\res ee G tn u. ?cenv'.
      stmt_lands lctx sb res u /\ ~u.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
      cenv_top_ext cenv cenv' ee.scopes /\
      stmt_state_rel ctx func cenv' cx ee u /\ ghost_inv d cenv' cx ee G tn u /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z u = SOME w) /\
      (!z. not_fresh_at sa z ==> FLOOKUP G z = FLOOKUP G0 z /\
        op_taint tn (Var z) = op_taint tn0 (Var z)))
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `expr_body_pre cenv cx env e (es with gas_obs := [])` by fs[expr_body_pre_def] >>
  `expr_sim_ptr d ctx PG func cenv cx ty e (es with gas_obs := [])` by
    (qpat_x_assum `body_expr_ptr_ok _ _`
      (mp_tac o REWRITE_RULE [body_expr_ptr_ok_def]) >>
     disch_then (irule o cj 1 o CONJUNCT1) >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     (es with gas_obs := [])` by
    (rw[gas_admissible_def] >>
     `expr_body_pre cenv cx env e (es with gas_obs := gs)` by fs[expr_body_pre_def] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_res_ok) >> simp[]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`s1`,`s2`,`rhs`,`t`,`H`,`tm`] mp_tac) >>
  (impl_tac >- simp[ghost_inv_gas_obs]) >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "summary" >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (eval_target_place cx tgt)
     (es,s0,G0,tn0) [] (INL (StoragePlace tr slot tvt)) es H tm (OK t)` by
    simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
  drule_all augassign_storage_place_exempt_ptr >> disch_tac >>
  simp[gas_outcome_ptr_def] >> metis_tac[]
QED

Resume augassign_storage_place_pipeline_ptr[summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
  drule_all augassign_storage_place_exception_exec_ptr >>
  disch_then (qspecl_then [`ty`,`bop`] assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >> goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]
QED

Resume augassign_storage_place_pipeline_ptr[normal]:
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v',es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o cj 1 o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[]) >>
  `!gs. eval_target_place cx tgt (es with gas_obs := gs) =
      (INL (StoragePlace tr slot tvt),es with gas_obs := gs) /\
    read_place cx (StoragePlace tr slot tvt) (es with gas_obs := gs) =
      (INL v,es with gas_obs := gs) /\
    place_type_value cx (StoragePlace tr slot tvt) (es with gas_obs := gs) =
      (INL tvt,es with gas_obs := gs)` by
    (simp[read_place_def, place_type_value_def, return_def] >>
     metis_tac[read_storage_slot_gas_obs_ptr]) >>
  drule_all augassign_pure_prefix_binop_admissible >> disch_tac >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by fs[expr_body_pre_def] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >> strip_tac >> gvs[] >>
  `well_formed_type_value tvt` by metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type tvt v` by metis_tac[read_storage_slot_success_type] >>
  `eval_operand rhs t' = SOME (val_to_w256 v')` by
    (irule expr_val_rel_word >> fs[expr_post_def] >>
     goal_assum (drule_at Any) >> simp[word_value_type_word]) >>
  `eval_operand cur t' = SOME (val_to_w256 v) /\ eval_operand dst t' = SOME slot` by
    (conj_tac >> irule eval_operand_frame >> simp[] >> qexistsl [`s1`,`t`] >>
     fs[expr_post_def]) >>
  `op_prov G cur = NONE /\ op_taint tn cur = {}` by
    (Cases_on `cur` >> fs[ghost_kept_def, op_prov_def, op_taint_def]) >>
  `op_taint tn dst = {}` by
    (Cases_on `dst` >> fs[ghost_kept_def, op_taint_def]) >>
  `op_prov G rhs = NONE /\ op_taint tn rhs = {}` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def, word_value_type_word]) >>
  suspend "continuation"
QED

Resume augassign_storage_place_pipeline_ptr[continuation]:
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by fs[expr_sim_inv_def] >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!l. rhs <> Label l` by (drule_all lower_compile_expr_not_label >> simp[]) >>
  `!l. cur <> Label l /\ rhs <> Label l /\ dst <> Label l` by simp[] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t'` by fs[expr_post_def] >>
  `~t'.vs_halted` by
    (qpat_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
     metis_tac[gas_path_ptr_erase, fragGasPathTheory.gas_path_normal]) >>
  `(!z. cur = Var z ==> not_fresh_at s2 z) /\
   (!z. rhs = Var z ==> not_fresh_at s2 z) /\
   (!z. dst = Var z ==> not_fresh_at s2 z)` by
    (rpt conj_tac >> rpt strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono, compile_lower_value_var]) >>
  `(!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s2 z)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s1` >> simp[]) >>
  `?tv er. eval_expr cx e (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
      (INL tv,er) /\ read_result cx tv er = (INL v',es_end with gas_obs := [])` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `(bop = ShL \/ bop = ShR ==> ?i. v' = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount] >>
  `(bop = Exp ==> (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
     (!n. expr_int_literal e = SOME n ==> v' = IntV n))` by
    (strip_tac >> gvs[] >>
     fs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[] >> metis_tac[eval_expr_int_literal_agrees]) >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] v v' (es_end with gas_obs := []))` by
    simp[] >>
  drule augassign_storage_clean_continuation_ptr >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac)
  >- suspend "finish_normal" >> suspend "finish_abort"
QED

Resume augassign_storage_place_pipeline_ptr[finish_normal]:
  `!gs. eval_target_place cx tgt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tvt),es with gas_obs := gs)` by simp[] >>
  drule_all augassign_storage_place_normal_exec_ptr >> strip_tac >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z /\ not_fresh_at s2 z` by
    (fs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z t'' = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at s1 z /\ not_fresh_at s2 z` by simp[] >>
     `lookup_var z t = SOME w` by simp[] >>
     `lookup_var z t' = SOME w` by
       (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
          (mp_tac o cj 4 o REWRITE_RULE [expr_post_def]) >> simp[]) >>
     metis_tac[]) >>
  `!z. not_fresh_at sa z ==> FLOOKUP H' z = FLOOKUP G0 z /\
       op_taint tm' (Var z) = op_taint tn0 (Var z)` by
    (rpt strip_tac >>
     `not_fresh_at s1 z /\ not_fresh_at s2 z` by simp[] >>
     fs[ghost_kept_def]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >> goal_assum (drule_at Any) >> disj1_tac >>
  simp[stmt_lands_def, cenv_top_ext_refl, ghost_inv_gas_obs]
QED

Resume augassign_storage_place_pipeline_ptr[finish_abort]:
  `!gs. eval_target_place cx tgt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tvt),es with gas_obs := gs)` by simp[] >>
  drule_all augassign_storage_place_normal_exec_ptr >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >> goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def, expr_exit_def, exit_result_def]
QED

Finalise augassign_storage_place_pipeline_ptr
