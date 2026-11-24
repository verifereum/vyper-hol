(* The operator and selected store use the operands captured by the RHS run. *)
Theory bodyAugOperatorToWriteMods
Ancestors
  bodyAugRhsOperatorReadyMods bodyAugOperatorSuccessMods bodyAugOperatorErrorMods
  bodyAugSelectedWriteMods bodyAugGuardedPrefixMods gasOutcomeFullPostMods
  bodyMemoryDefs bodyFullShadowBodyInv bodyFullPostsMods bodyPtrDefs loweringPosts
  exprSafeOperand freshWrites ptrDiscipline stateFrame vyperState vyperStorageTrace vyperStorageFootprint

val aug_binop = ``evaluate_binop
  (case type_to_int_bound ty of SOME n => n | NONE => Unsigned 0)
  ptv bop cur rhs``;

val aug_stmt_exit = ``\(H : (bool # 256 word # type_value) list # num list) res es (gt : (string |-> num # num) # taint) r.
  (!tail. stmt_exit_ptr (RetQ H) (es with gas_obs := tail) res gt r) /\
  halt_exit H cx es res r /\
  (ctx_has_dalloca ctx ==>
    !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)``;

val aug_write_common = ``
  gas_admissible (write_place cx p value) (stmt_res_ok lctx) ee /\
  expr_sim_inv_mods mods cenv cx env ee /\
  target_ptr_ok cenv (PlaceR p) r Gw tnw w /\
  eval_operand result w = SOME (typed_val_to_w256 ptv value) /\ op_taint tnw result = {} /\
  (!x. result = Var x ==> not_fresh_at s3 x) /\ local_ptrs_reserved cenv s3 /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
  ~w.vs_halted /\ w.vs_current_bb = s3.cs_current_bb /\ w.vs_inst_idx = LENGTH s3.cs_current_insts /\
  fn_has_code s3 sf func /\ is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv /\
  value_has_type ptv value /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee w /\ immutable_frame_mods func cenv cx ee w /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gw tnw w /\
    return_buf_frame d cenv s3 w /\ return_buf_sep d cenv ee w /\
    alloca_history func w /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
    s0.vs_alloca_next <= w.vs_alloca_next /\
    (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x w = SOME z) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP w.vs_allocas aid = SOME b) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gw tnw /\ alloca_frame cenv es sa s0 cenv ee w)``;

val aug_write_result = ``
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (write_place cx p value) (ee,w,Gw,tnw) stmtQ ^aug_stmt_exit``;

Theorem augassign_operator_to_selected_write_mods:
  contract_inv mods exps ctx cenv cx /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  (!gs. eval_target_place cx bt (es with gas_obs := preT ++ gs) =
        (INL p,mid with gas_obs := gs)) /\ mid.gas_obs = [] /\
  read_place cx p mid = (INL cur,mid) /\ place_type_value cx p mid = (INL ptv,mid) /\
  evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv cur /\
  (!gs. bind (eval_expr cx e) (read_result cx) (mid with gas_obs := preE ++ gs) =
        (INL rhs,ee with gas_obs := gs)) /\ ee.gas_obs = [] /\
  expr_body_pre_mods mods cenv cx env e mid /\
  expr_sim_inv_mods mods cenv cx env mid /\ ~aug_assign_overlap cenv bt e /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sT s0 mid
         (PlaceR p) (Type ty) r G0 tn0 Gtarget tnt t /\
       stmt_state_rel H ctx func cenv cx mid u /\
       wb_frame cenv es mid sa s0 u /\ ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tu /\
       (!id path. p = MemoryPlace id path ==>
          ?entry old. lookup_scopes id mid.scopes = SOME entry /\
                     evaluate_subscripts entry.type entry.value path = INL old)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       expr_post_mods H ctx func cenv cx e mid s1 s2 u ee rhs rhsop q /\
       ptr_val_ok cx (post_value_type cenv e) rhs rhsop Gq tq q /\
       ghost_kept_at lo cenv mid s1 Gu tu u Gq tq /\
       ghost_inv_at_mods (DF H) lo d cenv cx ee Gq tq q) /\
  lower_value compile_expr cenv ty e s1 = (rhsop,s2) /\
  compile_binop bop old rhsop ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sT /\ local_ptrs_reserved cenv s2 /\
  ci_mono sa sT /\ ci_mono sT s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
  (!x. FST r = Var x ==> not_fresh_at s1 x) /\
  (!x z. not_fresh_at sT x /\ lookup_var x t = SOME z ==> lookup_var x u = SOME z) /\
  return_buf_frame d cenv s1 u /\ return_buf_sep d cenv es s0 /\
  (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) q) /\
  alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
  s0.vs_alloca_next <= u.vs_alloca_next /\ u.vs_alloca_next <= q.vs_alloca_next /\
  ~q.vs_halted /\ q.vs_current_bb = s2.cs_current_bb /\ q.vs_inst_idx = LENGTH s2.cs_current_insts /\
  eval_operand (FST r) t = SOME addr /\ eval_operand (FST r) q = SOME addr /\
  target_ptr_ok cenv (PlaceR p) r Gq tq q /\
  op_prov Gu (FST r) = op_prov Gtarget (FST r) /\
  (!x. old = Var x ==> not_fresh_at s1 x) /\ (!l. old <> Label l) /\
  eval_operand old q = SOME (typed_val_to_w256 ptv cur) /\
  op_prov Gq old = NONE /\ op_taint tq old = {} /\
  FST (SND r) = SOME loc /\
  (if loc = LocCode then compile_ptr_store cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r) result
   else emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
                  [FST r; result]) s3 = ((),sf) /\
  (!value w Gw tnw tr slot root rtv path delta res ff.
     p = StoragePlace tr slot ptv /\ MEM (StorageRoot tr root rtv) ee.storage_trace /\
     storage_subregion rtv path delta ptv /\ slot = n2w root + n2w delta /\
     write_place cx p value ee = (res,ff) /\ stmt_res_ok lctx res /\
     emit_void (if tr then TSTORE else SSTORE) [FST r;result] s3 = ((),sf) /\
     eval_operand (FST r) w = SOME slot /\ op_taint tnw (FST r) = {} /\
     ^aug_write_common ==> ^aug_write_result) /\
  (!value w Gw tnw id path entry old res ff.
     p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL old /\
     place_ptr_rel cenv cx w (PlaceR p) addr (SOME LocMemory) (Type ty) /\
     store_lays_out ptv ptv value /\ write_place cx p value ee = (res,ff) /\ stmt_res_ok lctx res /\
     emit_void MSTORE [FST r;result] s3 = ((),sf) /\ eval_operand (FST r) w = SOME addr /\
     ^aug_write_common ==> ^aug_write_result) /\
  (!value w Gw tnw owner id path tops imms itv now off k ff.
     p = ImmutablePlace owner id path /\ cenv.ce_is_ctor /\
     ALOOKUP cenv.ce_modules owner = SOME tops /\ ALOOKUP ee.immutables cx.txn.target = SOME imms /\
     FLOOKUP (get_source_immutables owner imms) id = SOME (itv,now) /\
     FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
     mem_path_offset itv path = SOME (k,ptv) /\ write_place cx p value ee = (INL (),ff) /\
     compile_imm_store_word cenv.ce_imm_alloca (FST r) result s3 = ((),sf) /\
     eval_operand (FST r) w = SOME (n2w (off+k)) /\ op_taint tnw (FST r) = {} /\
     op_prov Gw (FST r) = NONE /\ ^aug_write_common ==> ^aug_write_result) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (vyperState$lift_sum ^aug_binop) (write_place cx p)) (ee,q,Gq,tq) stmtQ ^aug_stmt_exit
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all_then strip_assume_tac augassign_rhs_operator_ready_mods >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       allocas_from lo q /\ lo <= q.vs_alloca_next` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> fs[ghost_inv_at_mods_def]) >>
  Cases_on `^aug_binop`
  >- suspend "value" >>
  suspend "abort"
QED

Resume augassign_operator_to_selected_write_mods[value]:
  rename1 `^aug_binop = INL value` >>
  qpat_x_assum `case INL value of INL _ => _ | INR _ => _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [sumTheory.sum_case_def]) >>
  `?w Gw tnw.
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (q,Gq,tq) [] (OK w,Gw,tnw)) /\
      expr_val_rel cx ty value result w /\ eval_operand result w = SOME (typed_val_to_w256 ptv value) /\
      op_prov Gw result = NONE /\ op_taint tnw result = {} /\
      ~w.vs_halted /\ w.vs_current_bb = s3.cs_current_bb /\
      w.vs_inst_idx = LENGTH s3.cs_current_insts /\
      s3.cs_current_bb = s2.cs_current_bb /\ s2.cs_next_var <= s3.cs_next_var /\
      s3.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 s3 /\
      EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts s2 s3) /\
      state_frame w = state_frame (q with vs_inst_idx := w.vs_inst_idx) /\
      tnw.t_mem = tq.t_mem /\ tnw.t_stor = tq.t_stor /\
      tnw.t_trans = tq.t_trans /\ tnw.t_imm = tq.t_imm /\
      (!z. not_fresh_at s2 z ==> lookup_var z w = lookup_var z q /\
           FLOOKUP Gw z = FLOOKUP Gq z /\ op_taint tnw (Var z) = op_taint tq (Var z)) /\
      eval_operand old w = SOME (typed_val_to_w256 ptv cur) /\
      eval_operand rhsop w = SOME (typed_val_to_w256 tvR rhs) /\
      op_prov Gw old = NONE /\ op_taint tnw old = {} /\
      op_prov Gw rhsop = NONE /\ op_taint tnw rhsop = {}` by
    suspend "operator_success" >>
  simp[lift_sum_def, bind_return] >>
  irule augassign_zero_prefix_guarded_mods >>
  simp[storage_trace_frame_write_place] >>
  qexistsl_tac [`Gw`,`w`,`tnw`] >> simp[] >> suspend "selected_store"
QED

Resume augassign_operator_to_selected_write_mods[operator_success]:
  irule augassign_operator_success_path_mods >>
  rpt (first_assum (irule_at Any)) >>
  simp[] >> conj_tac >-
    (rpt strip_tac >> qpat_assum `!H. _ ==> allocas_from _ _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Resume augassign_operator_to_selected_write_mods[selected_store]:
  `!gs. eval_stmt cx (AugAssign ty bt bop e) (es with gas_obs := (preT ++ preE) ++ gs) =
        write_place cx p value (ee with gas_obs := gs)` by simp[lift_sum_def, bind_return] >>
  `mid with gas_obs := [] = mid /\ ee with gas_obs := [] = ee` by
    simp[evaluation_state_component_equality] >>
  `eval_target_place cx bt (es with gas_obs := preT) = (INL p,mid)` by
    (qpat_assum `!gs. eval_target_place _ _ _ = _` (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >> asm_rewrite_tac[]) >>
  `bind (eval_expr cx e) (read_result cx) (mid with gas_obs := preE) = (INL rhs,ee)` by
    (qpat_assum `!gs. bind (eval_expr _ _) _ _ = _` (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >> asm_rewrite_tac[]) >>
  `expr_body_pre_mods mods cenv cx env e (mid with gas_obs := preE)` by simp[] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
        expr_post_mods H ctx func cenv cx e mid s1 s2 u ee rhs rhsop q /\
        ghost_kept_at lo cenv mid s1 Gu tu u Gq tq /\ storage_well_formed_on cx ee (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee Gq tq q` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ ptr_val_ok _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
     >- (qpat_x_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[expr_post_mods_def,expr_post_def] >> strip_tac >>
         first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC) >>
  `return_buf_frame d cenv s2 q` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`u`,`s1`] >>
     qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >> simp[]) >>
  `w.vs_allocas = q.vs_allocas /\ w.vs_fmp = q.vs_fmp /\
   w.vs_initial_fmp = q.vs_initial_fmp` by
    (qpat_assum `state_frame w = _` mp_tac >> simp[state_frame_def]) >>
  `(!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) w) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp w)` by
    (conj_tac
     >- (qpat_x_assum `!bw cap. d = SOME _ ==> allocas_from _ q` mp_tac >>
         simp_tac bool_ss [allocas_from_def] >> asm_rewrite_tac[]) >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp q` mp_tac >>
     simp_tac bool_ss [allocas_below_fmp_def] >> asm_rewrite_tac[]) >>
  `!x. FST r = Var x ==> not_fresh_at s2 x` by metis_tac[not_fresh_at_mono] >>
  `op_prov Gtarget (FST r) = NONE ==> op_prov Gq (FST r) = NONE` by
    (qpat_assum `ghost_kept_at lo cenv mid s1 _ _ _ _ _` mp_tac >>
     qpat_assum `!x. FST r = Var x ==> not_fresh_at s1 x` mp_tac >>
     qpat_assum `op_prov Gu (FST r) = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `FST r` >>
     simp[op_prov_def,ghost_kept_at_def] >> metis_tac[]) >>
  drule_then strip_assume_tac (REWRITE_RULE [safe_operand_def] compile_binop_safe_operand) >>
  qpat_assum `!v w G tn tr slot root rtv path delta res ff. p = StoragePlace _ _ _ /\ _ ==> _`
    (qspecl_then [`value`,`w`,`Gw`,`tnw`] assume_tac) >>
  qpat_assum `!v w G tn id path entry old res ff. p = MemoryPlace _ _ /\ _ ==> _`
    (qspecl_then [`value`,`w`,`Gw`,`tnw`] assume_tac) >>
  qpat_assum `!v w G tn owner id path tops imms itv now off k ff. p = ImmutablePlace _ _ _ /\ _ ==> _`
    (qspecl_then [`value`,`w`,`Gw`,`tnw`] assume_tac) >>
  mp_tac (Q.INST [`prefix` |-> `preT ++ preE`, `reads` |-> `preT`,
                  `rhsReads` |-> `preE`, `stmtR` |-> `^aug_stmt_exit`]
                 (SPEC_ALL augassign_selected_write_mods)) >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> asm_rewrite_tac[]
QED

Resume augassign_operator_to_selected_write_mods[abort]:
  rename1 `^aug_binop = INR err` >>
  qpat_x_assum `case INR err of INL _ => _ | INR _ => _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [sumTheory.sum_case_def]) >>
  qpat_x_assum `err = RuntimeError _` SUBST_ALL_TAC >>
  `?w Gw tnw. !H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (q,Gq,tq) []
         (Abort Revert_abort w,Gw,tnw) /\
       w.vs_allocas = q.vs_allocas /\ w.vs_alloca_next = q.vs_alloca_next /\
       allocas_from lo w /\ lo <= w.vs_alloca_next` by
    suspend "operator_error" >>
  irule gas_outcome_full_mods_exit >>
  (reverse conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gw`,`ee`,`Abort Revert_abort w`,`INR (Error (RuntimeError msg))`,`tnw`] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[lift_sum_def,bind_def,raise_def,fragExecTheory.exit_result_def,
       stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ [] (Abort Revert_abort w,_,_) /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC
QED

Resume augassign_operator_to_selected_write_mods[operator_error]:
  irule (SIMP_RULE (srw_ss()) [stmt_exit_ptr_def,exprSimDefsTheory.expr_exit_def,
                               exprSimDefsTheory.halt_exit_def] augassign_operator_error_path_mods) >>
  qpat_assum `compile_binop _ old rhsop _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `bop_result _ _ _ _ _ _ ee = _` (irule_at Any) >>
  rpt (first_assum (irule_at Any)) >> simp[] >>
  rpt strip_tac >> qpat_assum `!H. _ ==> allocas_from _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Finalise augassign_operator_to_selected_write_mods
