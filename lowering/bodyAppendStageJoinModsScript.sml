(* Append evaluates the target before its element. These joins use the
   counted endpoints of those evaluations, not new runs of either child. *)
Theory bodyAppendStageJoinMods
Ancestors
  bodyWriteTargetStageMods bodyPlacePairedStagesMods bodyFullPredsMods
  bodyAppendStorageFacts gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods gasContext exprSimDefs stmtSimDefs haltExitProj
  vyperExprNoControl vyperStorageTrace vyperStorageFootprint
  popTargetPre bodySim allocLimits exprLowering targetPlaceSimCases
  bodyFullShadowBodyInv fragExec vyperState bodyPtrDefs stmtSimProps loweringPosts
  exprLoweringProps bodyMemoryDefs bodyFullPostsMods
Libs monadsyntax

Definition append_exit_mods_def[nocompute]:
  append_exit_mods ctx cx RetQ H res ee gt r <=>
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
    halt_exit H cx ee res r /\
    (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==>
       allocas_below_fmp s)
End

Theorem append_expr_exit_mods[local]:
  expr_exit (res : 'a + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  ?exc. res = INR exc /\ append_exit_mods ctx cx RetQ H (INR exc) ee gt r
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  simp[append_exit_mods_def, GSYM expr_exit_def, stmt_exit_ptr_def,
       expr_exit_INR_type, halt_exit_INR_type] >>
  Cases_on `r` >> simp[expr_exit_def]
QED

Theorem append_target_admissible_mods[local]:
  gas_admissible (eval_stmt cx (Append bt e)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `INR exc` >>
  `no_control_exc exc` by metis_tac[eval_target_place_no_control] >>
  `stmt_res_ok lctx (INR exc)` by
    (drule gas_admissible_result >> disch_then irule >>
     qexistsl [`ee`,`gs`] >> simp[append_source_stages_mods, Once bind_def]) >>
  gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]
QED

Theorem append_typed_place_bind_mods[local]:
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es /\
  type_place_target env bt = SOME (Type (ArrayT elem (Dynamic cap))) /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  gas_admissible (eval_stmt cx (Append bt e)) (stmt_res_ok lctx) es /\
  (!marks p mid Gm tm t.
    (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL p,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    (!id path. p = MemoryPlace id path ==>
      ?entry v. lookup_scopes id mid.scopes = SOME entry /\
                evaluate_subscripts entry.type entry.value path = INL v) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0
        mid (PlaceR p) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0
      (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
      (mid,t,Gm,tm) Q (append_exit_mods ctx cx RetQ)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (Append bt e))
    (es,s0,G0,tn0) Q (append_exit_mods ctx cx RetQ)
Proof
  strip_tac >> drule_then assume_tac append_target_admissible_mods >>
  qpat_x_assum `write_place_sim_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [write_place_sim_mods_def]) >>
  disch_then (qspecl_then [`st0`,`ArrayT elem (Dynamic cap)`,`sa`,`sp`,
    `shadow_sa`,`shadow_sp`,`dst`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ChildQ ChildR` >>
  rewrite_tac[append_source_stages_mods] >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_place >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!p. storage_trace_frame (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))`]
  >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
          storage_trace_frame_read_result, storage_trace_frame_append_place] >>
  qexists `\H res ee G tn t. ChildQ H res ee G tn t /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `ChildR`, Excl "AND_IMP_INTRO"] >>
      rpt gen_tac >> disch_tac >> irule append_expr_exit_mods >> simp[]) >>
  suspend "target_reached"
QED

Resume append_typed_place_bind_mods[target_reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`Gm`,`tm`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ChildQ (storage_trace_horizon mid.storage_trace) res mid Gm tm t /\ mid.gas_obs = []` by
    (first_x_assum drule >> simp[]) >>
  qpat_x_assum `ChildQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
  simp[Abbr `ChildQ`,NoAsms] >>
  disch_then (qx_choose_then `p` (CONJUNCTS_THEN2 SUBST_ALL_TAC strip_assume_tac)) >>
  disj1_tac >> qexists `p` >> simp[] >>
  first_x_assum irule >> conj_tac
  >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED

Finalise append_typed_place_bind_mods[local]

(* The lower-value post before either the word append or its copy suffix. *)
Definition append_rhs_post_mods_def[nocompute]:
  append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm
    H v ee G tn u <=>
    expr_post_mods H ctx func cenv cx e mid sp sm t ee v op u /\
    expr_store_bound cx (post_value_type cenv e) v op u /\
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    t.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn u /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G u) /\
    ghost_kept_at lo cenv mid sp Gm tm t G tn
End

Theorem append_rhs_bind_mods[local]:
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (mid,t,Gm,tm)
    (\H res ee G tn u. ?v. res = INL v /\
      append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) /\
  (!marks v ee G tn u.
    (!tail. bind (eval_expr cx e) (read_result cx)
      (mid with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail) =
        (INL v,ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~u.vs_halted /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u) ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (append_place cx p v) (ee,u,G,tn) Q
      (append_exit_mods ctx cx RetQ)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))
    (mid,t,Gm,tm) Q (append_exit_mods ctx cx RetQ)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx e) (read_result cx)) _ ChildQ ChildR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) (read_result _))`]
  >- simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`!v. storage_trace_frame (append_place cx p v)`]
  >- simp[storage_trace_frame_append_place] >>
  qexists `\H res ee G tn u. ChildQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >> first_assum (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `ChildR`, Excl "AND_IMP_INTRO"] >>
      rpt gen_tac >> disch_tac >> irule append_expr_exit_mods >> simp[]) >>
  suspend "rhs_reached"
QED

Resume append_rhs_bind_mods[rhs_reached]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`u`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ChildQ (storage_trace_horizon ee.storage_trace) res ee G tn u /\
   ee.gas_obs = [] /\ ~u.vs_halted` by (first_x_assum drule >> simp[]) >>
  qpat_x_assum `ChildQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
  simp[Abbr `ChildQ`, NoAsms] >>
  disch_then (qx_choose_then `v` (CONJUNCTS_THEN2 SUBST_ALL_TAC assume_tac)) >>
  disj1_tac >> qexists `v` >> simp[] >>
  first_x_assum irule >> conj_tac
  >- (qexists `marks` >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[]
QED

Finalise append_rhs_bind_mods[local]

Theorem append_place_routes_mods[local]:
  stmt_exprs_ok cenv (Append bt e) /\
  write_target_post_mods H D lo d ctx func cenv cx bt es sa sp s0 mid
    (PlaceR p) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t ==>
  SND (SND dst) = SOME (ValPT (ArrayT elem (Dynamic cap))) /\
  ((?id path. p = MemoryPlace id path /\ FST (SND dst) = SOME LocMemory) \/
   (?tr slot tv. p = StoragePlace tr slot tv /\ FST (SND dst) = SOME (slot_loc tr)))
Proof
  strip_tac >> drule_then strip_assume_tac write_target_post_view_mods >>
  simp[value_type_place_def] >> Cases_on `p` >>
  gvs[write_target_location_mods_def, place_ptr_rel_def] >>
  fs[stmt_exprs_ok_def, alloc_limits_stmt_def, target_in_immutables_root] >> metis_tac[]
QED

Definition append_rhs_code_mods_def[nocompute]:
  append_rhs_code_mods cenv e elem sp sm shadow_sp shadow_sm op func shadow_func <=>
    lower_value compile_expr cenv elem e sp = (op,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) elem (gas_shadow_expr e)
      shadow_sp = (op,shadow_sm) /\
    gas_shadow_state sp shadow_sp /\ gas_shadow_state sm shadow_sm /\
    fn_has_code sp sm func /\ fn_has_code shadow_sp shadow_sm shadow_func
End

Theorem append_rhs_admissible_mods[local]:
  gas_admissible (eval_stmt cx (Append bt e)) (stmt_res_ok lctx) es /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
      (INL p,mid with gas_obs := tail)) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid
Proof
  strip_tac >> rw[gas_admissible_def] >> Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def, AllCaseEqs()] >>
     strip_tac >> gvs[]
     >- metis_tac[read_result_no_control] >> metis_tac[cj 1 eval_expr_no_control]) >>
  `stmt_res_ok lctx (INR ex)` by
    (drule gas_admissible_result >> disch_then irule >> qexistsl [`ee`,`prefix ++ gs`] >>
     simp[append_source_stages_mods, Once bind_def] >> simp[Once bind_def]) >>
  gvs[stmt_res_ok_def, expr_res_ok_def, no_control_exc_def]
QED

(* The expression child is called only at a replay witness for the target.
   The target post is used at the RHS entry for every valid horizon. *)
Theorem append_rhs_from_place_mods[local]:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env mid /\ expr_body_pre_mods mods cenv cx env e mid /\
  (!s p s'. eval_target_place cx bt s = (INL p,s') ==> body_expr_full_ok_mods mods exps cx e) /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL p,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
  gas_admissible (eval_stmt cx (Append bt e)) (stmt_res_ok lctx) es /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  append_rhs_code_mods cenv e elem sp sm shadow_sp shadow_sm op func shadow_func /\
  ci_mono sa sp /\
  (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0
      mid (PlaceR p) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (mid,t,Gm,tm)
    (\H res ee G tn u. ?v. res = INL v /\
      append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all_then assume_tac append_rhs_admissible_mods >>
  `body_expr_full_ok_mods mods exps cx e` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _` (qspec_then `[]` assume_tac) >>
     first_x_assum irule >> rpt (goal_assum (drule_at Any))) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx elem e mid` by
    (qpat_assum `body_expr_full_ok_mods _ _ _ _`
       (mp_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     strip_tac >> qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es. _ ==> _`
       (drule_all_then (mp_tac o SIMP_RULE bool_ss [FORALL_AND_THM])) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >>
  fs[write_target_entry_mods_def, append_rhs_code_mods_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid Gm tm t` by
    (gen_tac >> disch_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then (strip_assume_tac o MATCH_MP write_target_post_view_mods)) >> simp[]) >>
  `sa.cs_next_var <= sp.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sp` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `return_buf_frame d cenv sp t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> fs[wb_frame_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sp x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sp`,`sm`,`shadow_sp`,`shadow_sm`,`op`,`t`,`Gm`,`tm`] mp_tac) >>
  simp[append_rhs_post_mods_def] >> disch_then irule >> first_assum ACCEPT_TAC
QED

Definition append_store_code_mods_def[nocompute]:
  append_store_code_mods cenv e dst loc elem cap op sm sb func <=>
    if is_word_type elem then
      compile_dynarray_append cenv (FST dst) op (word_scale loc)
        (elem_size_in_location cenv loc elem) elem (lowered_value_type cenv e)
        cap T loc sm = ((),sb) /\ fn_has_code sm sb func
    else ?tmp sc sd.
      compile_alloc_buffer (type_memory_bytes cenv elem) sm = (tmp,sc) /\
      compile_store_memory cenv op tmp.buf_operand elem (lowered_value_type cenv e)
        sc = ((),sd) /\
      compile_dynarray_append cenv (FST dst) tmp.buf_operand (word_scale loc)
        (elem_size_in_location cenv loc elem) elem elem cap F loc sd = ((),sb) /\
      fn_has_code sm sc func /\ fn_has_code sc sd func /\ fn_has_code sd sb func
End

(* A landing rule receives the saved target and the reached expression post.
   Its guard selects a location/layout, not a different evaluation. *)
Definition append_landing_rule_mods_def[nocompute]:
  append_landing_rule_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt e elem cap es st0 sa sp sm sb dst op s0 G0 tn0 RetQ Q selected <=>
    !l marks p mid Gm tm t rhsmarks v ee G tn u.
      selected p /\ FST (SND dst) = SOME l /\
      append_store_code_mods cenv e dst l elem cap op sm sb func /\
      (!tail. eval_target_place cx bt
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL p,mid with gas_obs := tail)) /\
      storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
      (!id path. p = MemoryPlace id path ==>
        ?entry w. lookup_scopes id mid.scopes = SOME entry /\
                  evaluate_subscripts entry.type entry.value path = INL w) /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0
          mid (PlaceR p) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t) /\
      (!tail. bind (eval_expr cx e) (read_result cx)
        (mid with gas_obs := gas_explicit rhsmarks t.vs_gas_readings ++ tail) =
          (INL v,ee with gas_obs := tail)) /\
      storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~u.vs_halted /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        append_rhs_post_mods DF lo d ctx func cenv cx e mid sp sm t op Gm tm H v ee G tn u) ==>
      gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cenv.ce_modules cx st0 (append_place cx p v) (ee,u,G,tn) Q
        (append_exit_mods ctx cx RetQ)
End

(* The RHS source/frame producer is separate: it is used only at a normal
   target endpoint. The paired cut can still carry compiler fallback selectors;
   on that endpoint typing fixes the compiled location, element, and capacity. *)
Theorem append_staged_routes_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  type_place_target env bt = SOME (Type (ArrayT elem (Dynamic cap))) /\
  stmt_exprs_ok cenv (Append bt e) /\
  (!s p s'. eval_target_place cx bt s = (INL p,s') ==> body_expr_full_ok_mods mods exps cx e) /\
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt es st0 sa sp shadow_sa shadow_sp dst s0 G0 tn0 /\
  ci_mono sa sp /\
  gas_admissible (eval_stmt cx (Append bt e)) (stmt_res_ok lctx) es /\
  (let loc = (case FST (SND dst) of NONE => LocMemory | SOME l => l) in
   let et = (case SND (SND dst) of SOME (ValPT (ArrayT ty _)) => ty | _ => BaseT (UintT 256)) in
   let n = (case SND (SND dst) of SOME (ValPT (ArrayT _ (Dynamic n))) => n | _ => 0) in
     append_rhs_code_mods cenv e et sp sm shadow_sp shadow_sm op func shadow_func /\
     append_store_code_mods cenv e dst loc et n op sm sb func) /\
  (!marks p mid Gm tm t.
    (!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (INL p,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      write_target_post_mods H (DF H) lo d ctx func cenv cx bt es sa sp s0
        mid (PlaceR p) (Type (ArrayT elem (Dynamic cap))) dst G0 tn0 Gm tm t) ==>
    body_const_cells_agree_mods mods cx env mid /\ expr_body_pre_mods mods cenv cx env e mid /\
    (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s)) /\
  append_landing_rule_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt e elem cap es st0 sa sp sm sb dst op s0 G0 tn0 RetQ Q
    (\p. ?id path. p = MemoryPlace id path) /\
  append_landing_rule_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt e elem cap es st0 sa sp sm sb dst op s0 G0 tn0 RetQ Q
    (\p. is_word_type elem /\ ?tr slot tv. p = StoragePlace tr slot tv) /\
  append_landing_rule_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt e elem cap es st0 sa sp sm sb dst op s0 G0 tn0 RetQ Q
    (\p. ~is_word_type elem /\ ?tr slot tv. p = StoragePlace tr slot tv) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_stmt cx (Append bt e))
    (es,s0,G0,tn0) Q (append_exit_mods ctx cx RetQ)
Proof
  strip_tac >> irule append_typed_place_bind_mods >>
  conj_tac >- (qexists `lctx` >> simp[]) >>
  qexistsl_tac [`cap`,`d`,`dst`,`elem`,`env`,`sa`,`shadow_func`,`shadow_sa`,`shadow_sp`,`sp`] >> simp[] >>
  qx_genl_tac [`marks`,`p`,`mid`,`Gm`,`tm`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then assume_tac) >>
  drule_all_then (CONJUNCTS_THEN2 assume_tac (mk_asm "place_route")) append_place_routes_mods >>
  suspend "landing"
QED

Resume append_staged_routes_mods[landing]:
  `body_const_cells_agree_mods mods cx env mid /\ expr_body_pre_mods mods cenv cx env e mid /\
   (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s)` by
    (qpat_assum `!marks p mid Gm tm t. _ ==> body_const_cells_agree_mods _ _ _ _ /\ _`
       (drule_all_then ACCEPT_TAC)) >>
  `?l. FST (SND dst) = SOME l` by (asm "place_route" strip_assume_tac >> metis_tac[]) >>
  `append_rhs_code_mods cenv e elem sp sm shadow_sp shadow_sm op func shadow_func /\
   append_store_code_mods cenv e dst l elem cap op sm sb func` by
    (qpat_x_assum `let _ = _ in _` mp_tac >> simp[]) >>
  drule_all_then assume_tac append_rhs_from_place_mods >>
  irule append_rhs_bind_mods >> qexistsl_tac [`d`,`op`,`sm`,`sp`] >> simp[] >>
  qx_genl_tac [`rhsmarks`,`v`,`ee`,`G`,`tn`,`u`] >> strip_tac >>
  `?selected. selected p /\
    append_landing_rule_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx bt e elem cap es st0 sa sp sm sb dst op s0 G0 tn0 RetQ Q selected` by
    (asm "place_route" strip_assume_tac
     >- (qexists `\p. ?id path. p = MemoryPlace id path` >> simp[]) >>
     Cases_on `is_word_type elem`
     >- (qexists `\p. is_word_type elem /\ ?tr slot tv. p = StoragePlace tr slot tv` >> simp[]) >>
     qexists `\p. ~is_word_type elem /\ ?tr slot tv. p = StoragePlace tr slot tv` >> simp[]) >>
  qpat_x_assum `append_landing_rule_mods _ cenv cx bt e elem cap es
     st0 sa sp sm sb dst op s0 G0 tn0 RetQ Q selected`
    (drule_all_then ACCEPT_TAC o REWRITE_RULE [append_landing_rule_mods_def])
QED

Finalise append_staged_routes_mods
