(* The AugAssign RHS runs only after all three source-place tests. *)
Theory bodyAugToStoreMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods augAssignFullSaved augAssignFullRhsSaved
  stmtSimAugAssignPlaceMemory gasOutcomeFullMods fragGasOriginPtr fragGasOrigin
  fragExec
  bodyAugTargetBindMods bodyAugSelectedLoadMods bodyAugLoadedRhsMods
  bodyAugValueBindMods bodyAugOperatorToWriteMods bodyAugQueryPrefixMods
  bodyAugGuardedPrefixMods exprBodyPreProps bodyInvCodeProps bodyFullShared
  vyperEvalPreservesScopes exprSimWordArgs stmtSimAugAssignPlace
  vyperStorageFootprint vyperStorageTrace vyperState bodyFullIfExpReach
  exprLoweringProps freshWrites ptrDiscipline gasOutcomeFullPostMods
  bodyWriteTargetStageMods loweringPosts

Theorem augassign_reached_rhs_sim_mods:
  (!s p t s3 cur t3 s4 ptv t4.
     eval_target_place cx target s = (INL p,t) /\
     read_place cx p s3 = (INL cur,t3) /\
     place_type_value cx p s4 = (INL ptv,t4) ==>
     body_expr_full_ok_mods mods exps cx e) /\
  eval_target_place cx target entry = (INL p,mid) /\
  read_place cx p mid = (INL cur,mid) /\
  place_type_value cx p mid = (INL ptv,mid) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env mid /\
  expr_body_pre_mods mods cenv cx env e mid ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e mid
Proof
  strip_tac >>
  `body_expr_full_ok_mods mods exps cx e` by metis_tac[] >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  strip_tac >>
  qpat_x_assum `!a b c d e f g h i j k l m n. _ ==>
      expr_sim_full_mods _ _ _ _ _ _ /\ _` mp_tac >>
  metis_tac[]
QED

(* Refinement of the very same RHS execution, preserving the captured
   destination and old word.  The original outcome retains all nonnormal
   alternatives, including exemption in another module. *)
Theorem augassign_rhs_keep_operands_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R /\
  local_ptrs_reserved cenv sa /\
  (!x. FST place = Var x ==> not_fresh_at sa x) /\
  (!x. old = Var x ==> not_fresh_at sa x) /\
  eval_operand (FST place) s0 = SOME addr /\
  eval_operand old s0 = SOME word /\
  target_ptr_ok cenv (PlaceR p) place G0 tn0 s0 /\
  op_taint tn0 old = {} /\ op_prov G0 old = NONE ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. Q H res ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      eval_operand (FST place) t = SOME addr /\
      eval_operand old t = SOME word /\
      target_ptr_ok cenv (PlaceR p) place G tn t /\
      op_taint tn old = {} /\ op_prov G old = NONE) R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac
      >- (disj1_tac >> qexists_tac `t` >> gvs[] >>
          `t.vs_labels = s0.vs_labels` by
            metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
                      aug_place_marked_path_labels] >>
          drule_all_then strip_assume_tac augassign_saved_rhs_frame >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* A normal typed place selects the load, RHS, operator and write intervals.
   The only machine continuation assumed here is the selected physical write. *)
Theorem augassign_to_selected_store_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  is_word_type ty /\ ~aug_assign_overlap cenv bt e /\
  (!s p t s3 cur t3 s4 ptv t4.
     eval_target_place cx bt s = (INL p,t) /\
     read_place cx p s3 = (INL cur,t3) /\
     place_type_value cx p s4 = (INL ptv,t4) ==>
     body_expr_full_ok_mods mods exps cx e) /\
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sT shadow_sa shadow_sT r s0 G0 tn0 /\
  ci_mono sa sT /\ return_buf_sep d cenv es s0 /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  (FST (SND r) = NONE \/
   ?loc old rhsop result s1 s2 s3 shadow_s1 shadow_s2.
     FST (SND r) = SOME loc /\
     (if loc = LocCode then compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r)
      else emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
        [FST r]) sT = (old,s1) /\
     lower_value compile_expr cenv ty e s1 = (rhsop,s2) /\
     lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_s1 =
       (rhsop,shadow_s2) /\
     compile_binop bop old rhsop ty NONE
       (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
     (if loc = LocCode then compile_ptr_store cenv.ce_is_ctor cenv.ce_imm_alloca loc (FST r) result
      else emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
        [FST r;result]) s3 = ((),sf) /\
     gas_shadow_state s1 shadow_s1 /\ gas_shadow_state s2 shadow_s2 /\
     ci_mono sT s1 /\ ci_mono s1 s2 /\ ci_mono s2 s3 /\ ci_mono s3 sf /\
     fn_has_code sT s1 func /\ fn_has_code s1 s2 func /\
     fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
     fn_has_code shadow_s1 shadow_s2 shadow_func) /\
  (!reads p mid. eval_target_place cx bt (es with gas_obs := reads) = (INL p,mid) ==>
     body_const_cells_agree_mods mods cx env mid /\ expr_body_pre_mods mods cenv cx env e mid) /\
  (!p value ee w Gw tnw ptv result s3.
    gas_admissible (write_place cx p value) (stmt_res_ok lctx) ee /\
    expr_sim_inv_mods mods cenv cx env ee /\
    target_ptr_ok cenv (PlaceR p) r Gw tnw w /\
    eval_operand result w = SOME (typed_val_to_w256 ptv value) /\ op_taint tnw result = {} /\
    (!x. result = Var x ==> not_fresh_at s3 x) /\ local_ptrs_reserved cenv s3 /\
    (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
    (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at s3 x) /\
    ~w.vs_halted /\ w.vs_current_bb = s3.cs_current_bb /\ w.vs_inst_idx = LENGTH s3.cs_current_insts /\
    fn_has_code s3 sf func /\ evaluate_type (get_tenv cx) ty = SOME ptv /\ value_has_type ptv value /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee w /\ immutable_frame_mods func cenv cx ee w /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gw tnw w /\
      return_buf_frame d cenv s3 w /\ return_buf_sep d cenv ee w /\
      alloca_history func w /\ (ctx_has_dalloca ctx ==> allocas_below_fmp w) /\
      s0.vs_alloca_next <= w.vs_alloca_next /\
      (!x z. not_fresh_at sa x /\ lookup_var x s0 = SOME z ==> lookup_var x w = SOME z) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP w.vs_allocas aid = SOME b) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 Gw tnw /\ alloca_frame cenv es sa s0 cenv ee w) /\
    ((?tr slot root rtv path delta res ff.
       p = StoragePlace tr slot ptv /\ MEM (StorageRoot tr root rtv) ee.storage_trace /\
       storage_subregion rtv path delta ptv /\ slot = n2w root + n2w delta /\
       write_place cx p value ee = (res,ff) /\ stmt_res_ok lctx res /\
       emit_void (if tr then TSTORE else SSTORE) [FST r;result] s3 = ((),sf) /\
       eval_operand (FST r) w = SOME slot /\ op_taint tnw (FST r) = {}) \/
     (?id path entry previous addr res ff.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INL previous /\
       place_ptr_rel cenv cx w (PlaceR p) addr (SOME LocMemory) (Type ty) /\
       store_lays_out ptv ptv value /\ write_place cx p value ee = (res,ff) /\ stmt_res_ok lctx res /\
       emit_void MSTORE [FST r;result] s3 = ((),sf) /\ eval_operand (FST r) w = SOME addr) \/
     (?owner id path target_tops imms itv now off k ff.
       p = ImmutablePlace owner id path /\ cenv.ce_is_ctor /\
       ALOOKUP cenv.ce_modules owner = SOME target_tops /\ ALOOKUP ee.immutables cx.txn.target = SOME imms /\
       FLOOKUP (get_source_immutables owner imms) id = SOME (itv,now) /\
       FLOOKUP cenv.ce_module_vars (owner,id) = SOME (ImmutableLoc off) /\
       mem_path_offset itv path = SOME (k,ptv) /\ write_place cx p value ee = (INL (),ff) /\
       compile_imm_store_word cenv.ce_imm_alloca (FST r) result s3 = ((),sf) /\
       eval_operand (FST r) w = SOME (n2w (off+k)) /\ op_taint tnw (FST r) = {} /\
       op_prov Gw (FST r) = NONE)) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (write_place cx p value) (ee,w,Gw,tnw) Q
      (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (AugAssign ty bt bop e)) (es,s0,G0,tn0) Q
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  disch_then (EVERY o map assume_tac o CONJUNCTS) >>
  drule_then (assume_tac o CONJUNCT1) aug_place_typing >>
  irule augassign_typed_target_bind_mods >>
  rpt (first_assum (irule_at Any)) >>
  qx_genl_tac [`marks`,`p`,`mid`,`Gtarget`,`tt`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_then assume_tac augassign_reached_location_mods >>
  qpat_x_assum `FST (SND r) = NONE \/ _` strip_assume_tac >- fs[] >>
  suspend "load"
QED

Resume augassign_to_selected_store_mods[load]:
  qabbrev_tac `preT = gas_explicit marks s0.vs_gas_readings` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx bt (es with gas_obs := preT) = (INL p,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn upd =>
       qpat_assum `!tail. eval_target_place _ _ (_ with gas_obs := preT ++ tail) = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [listTheory.APPEND_NIL,upd])))) >>
  qpat_assum `!reads p mid. _ ==> body_const_cells_agree_mods _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sT s0 mid
         (PlaceR p) (Type ty) r G0 tn0 Gtarget tt t` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
      (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `local_ptrs_reserved cenv sT` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> fs[ci_mono_def]) >>
  drule_all augassign_selected_load_mods >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`addr`,`cur`,`ptv`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  suspend "loaded_rhs"
QED

Resume augassign_to_selected_store_mods[loaded_rhs]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >> rpt (first_assum (irule_at Any))) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (rpt strip_tac >> irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,Gtarget,tt)` (irule_at Any) >>
     qexists `fn` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e mid` by
    (irule augassign_reached_rhs_sim_mods >> rpt (first_assum (irule_at Any)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    (irule augassign_reached_rhs_admissible_mods >> rpt (first_assum (irule_at Any)) >>
     qexists `preT` >> first_assum ACCEPT_TAC) >>
  drule_all_then strip_assume_tac augassign_loaded_rhs_mods >>
  suspend "save_rhs"
QED

Resume augassign_to_selected_store_mods[save_rhs]:
  `?ys. mid.storage_trace = es.storage_trace ++ ys` by
    (qpat_assum `eval_target_place _ _ (es with gas_obs := preT) = _`
      (mp_then (Pat `f st = (res,st')`) mp_tac storage_trace_frame_prefix) >>
     simp[evaluate_storage_trace_frame]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) es.storage_trace` by
    (irule gasOutcomeFullTheory.valid_horizon_append >>
     qexists `ys` >>
     qpat_assum `mid.storage_trace = es.storage_trace ++ ys` (rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >> simp[]) >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t` by
    (rpt strip_tac >> irule return_buf_allocas_path >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t,Gtarget,tt)` (irule_at Any) >>
     rpt (first_assum (irule_at Any))) >>
  `!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) u` by
    (qpat_assum `u.vs_allocas = t.vs_allocas` (fn th =>
       PURE_REWRITE_TAC[allocas_from_def, th]) >>
     qpat_assum `!bw cap. d = SOME (bw,cap) ==> allocas_from _ t`
       (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `return_buf_sep d cenv mid u` by
    (qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `wb_frame cenv es mid sa s0 u`
       (assume_tac o CONJUNCT1 o REWRITE_RULE [wb_frame_def]) >>
     rpt (goal_assum (drule_at Any))) >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
    (fn rhs =>
       HO_PART_MATCH (fst o dest_conj o fst o dest_imp)
         augassign_rhs_keep_operands_mods (concl rhs)
       |> drule_all_then (mk_asm "saved_rhs")) >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ _ _` kall_tac >>
  asm_x "saved_rhs" assume_tac >>
  drule_all_then (mk_asm "rhs_allocas" o PURE_REWRITE_RULE [GSYM CONJ_ASSOC] o
    CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV (GSYM LEFT_EXISTS_AND_THM))) o BETA_RULE)
    gas_outcome_full_mods_return_buf_allocas >>
  simp_tac bool_ss [LET_THM, ETA_THM] >>
  ho_match_mp_tac augassign_read_type_prefix_mods >>
  rpt (first_assum (irule_at Any)) >>
  suspend "loaded_prefix"
QED

Resume augassign_to_selected_store_mods[loaded_prefix]:
  pure_once_rewrite_tac[GSYM bind_assoc] >>
  simp_tac (bool_ss ++ ETA_ss) [] >>
  irule augassign_zero_prefix_guarded_mods >>
  conj_tac
  >- (irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
           storage_trace_frame_read_result, storage_trace_frame_lifts,
           storage_trace_frame_write_place]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`Gu`,`u`,`tu`] >> conj_tac >- first_assum ACCEPT_TAC >>
  suspend "value_bind"
QED

Resume augassign_to_selected_store_mods[value_bind]:
  asm_x "rhs_allocas" (fn rhs =>
    mp_then Any irule
      (HO_PART_MATCH (fst o dest_conj o fst o dest_imp)
         augassign_typed_value_bind_mods (concl rhs)) rhs) >>
  qx_genl_tac [`rhsmarks`,`rhs`,`ee`,`Gq`,`tq`,`q`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  suspend "operator"
QED

Resume augassign_to_selected_store_mods[operator]:
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ _ _` kall_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (qpat_assum `write_target_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac write_target_post_view_mods) >>
     qpat_assum `u.vs_alloca_next = t.vs_alloca_next` (rewrite_tac o single) >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `s1.cs_next_var <= s2.cs_next_var` by
    first_assum (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o PURE_REWRITE_RULE [ci_mono_def]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists `s1` >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_then (once_rewrite_tac o single) contract_inv_cenv_modules >>
  irule (Q.INST [`preT` |-> `preT`, `preE` |-> `gas_explicit rhsmarks u.vs_gas_readings`,
                 `tnt` |-> `tt`] augassign_operator_to_selected_write_mods) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_assum `compile_binop _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `type_stmt _ _ (AugAssign _ _ _ _) = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `return_buf_sep _ _ es s0` (irule_at Any) >>
  qpat_assum `read_place _ _ _ = _` (irule_at Any) >>
  qpat_assum `op_prov _ (FST _) = op_prov _ (FST _)` (irule_at Any) >>
  qpat_assum `(if _ then compile_ptr_store _ _ _ _ _ else _) _ = _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ s1 u` (irule_at Any) >>
  qpat_assum `gas_admissible (eval_stmt _ _) _ _` (irule_at Any) >>
  (* The saved target and RHS prefixes fix the remaining endpoint witnesses. *)
  qexistsl [`tu`,`tt`,`tn0`,`t`,`sa`,`sT`,`rhsmarks`,`preT`,`addr`,`G0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      qpat_assum `!x. not_fresh_at _ x ==> lookup_var x _ = _ /\ _`
        (drule_then (assume_tac o CONJUNCT1)) >>
      simp[])
  >- suspend "return_buf_fresh"
  >- suspend "return_pc_fresh"
  >- suspend "rhs_horizon"
  >- suspend "entry_horizon"
  >- suspend "load_horizon"
  >- suspend "storage_write"
  >- suspend "memory_write"
  >- suspend "immutable_write"
QED

Resume augassign_to_selected_store_mods[return_buf_fresh]:
  rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `s1` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum (fn th => drule_then ACCEPT_TAC th)
QED

Resume augassign_to_selected_store_mods[return_pc_fresh]:
  rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `s1` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_assum (fn th => drule_then ACCEPT_TAC th)
QED

Resume augassign_to_selected_store_mods[rhs_horizon]:
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (MAP_EVERY assume_tac o CONJUNCTS)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume augassign_to_selected_store_mods[entry_horizon]:
  qx_gen_tac `H` >> strip_tac >>
  first_assum (fn th => drule_then (ACCEPT_TAC o CONJUNCT1) th)
QED

Resume augassign_to_selected_store_mods[load_horizon]:
  qx_gen_tac `H` >> strip_tac >> rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         first_assum (fn th => drule_then (fn post => FIRST (map ACCEPT_TAC (CONJUNCTS post))) th)]
QED

Resume augassign_to_selected_store_mods[storage_write]:
  qx_genl_tac [`value`,`w`,`Gw`,`tnw`,`tr`,`slot`,`root`,`rtv`,`path`,`delta`,`res`,`ff`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then (once_rewrite_tac o single o SYM) contract_inv_cenv_modules >>
  qpat_assum `!p value ee w Gw tnw ptv result s3. _ ==>
      gas_outcome_full_mods _ _ _ _ (write_place _ p value) _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`ptv`,`result`,`s3`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disj1_tac >> qexistsl [`tr`,`slot`,`root`,`rtv`,`path`,`delta`,`res`,`ff`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume augassign_to_selected_store_mods[memory_write]:
  qx_genl_tac [`value`,`w`,`Gw`,`tnw`,`id`,`path`,`entry`,`previous`,`res`,`ff`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then (once_rewrite_tac o single o SYM) contract_inv_cenv_modules >>
  qpat_assum `!p value ee w Gw tnw ptv result s3. _ ==>
      gas_outcome_full_mods _ _ _ _ (write_place _ p value) _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`ptv`,`result`,`s3`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >>
  qexistsl [`id`,`path`,`entry`,`previous`,`addr`,`res`,`ff`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume augassign_to_selected_store_mods[immutable_write]:
  qx_genl_tac [`value`,`w`,`Gw`,`tnw`,`owner`,`id`,`path`,`tops'`,`imms`,`itv`,`now`,`off`,`k`,`ff`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then (once_rewrite_tac o single o SYM) contract_inv_cenv_modules >>
  qpat_assum `!p value ee w Gw tnw ptv result s3. _ ==>
      gas_outcome_full_mods _ _ _ _ (write_place _ p value) _ _ _` irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl [`ptv`,`result`,`s3`] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disj2_tac >> disj2_tac >>
  qexistsl [`owner`,`id`,`path`,`tops'`,`imms`,`itv`,`now`,`off`,`k`,`ff`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise augassign_to_selected_store_mods
