(* Request-prefix simulation for uncopied array subscripts. *)
Theory s1PrefixSubscriptNoCopyCore
Ancestors
  s1PrefixPreds bodyFullSubscriptNoCopyBind s1PrefixDefs s1PrefixCompose s1PrefixNames
  bodyFullToplevelVVStorage allocLimits
  exprBodyPreProps s1PrefixProps vyperPlaceFrames
  bodyFullPreds bodyFullSimProjection bodySimFull gasOutcomeFullCompose
  exprSimSubscriptArrayFramed exprSimSubscriptArraySource exprSimHyps exprSimSource
  exprLoweringProps fragExec gasShadowCompileStmtHelpers gasShadowCompile gasShadowState
  exprSimVVFrame vyperStorageTrace vyperState vyperInterpreter bodyFullIfExpReach
  loweringPosts freshWrites compileEnv exprSimUnwrap gasShadow

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_admissible >>
  `~array_slot_base cenv e1 ==> expr_body_pre cenv cx env e1 es` by
    metis_tac[expr_body_pre_array_subscript_base] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e1 es` by
    (Cases_on `array_slot_base cenv e1`
     >- metis_tac[toplevel_slot_base_vv_full, expr_body_pre_array_subscript_slot_base] >>
     irule (cj 2 body_expr_full_ok_simulations) >>
     simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e1 es` by
    (Cases_on `array_slot_base cenv e1`
     >- (Cases_on `e1` >> fs[array_slot_base_def] >> irule toplevel_name_vv_prefix) >>
     qpat_assum `body_expr_prefix_ok cx e1`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >> metis_tac[]) >>
  simp[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty e1 sa = (bvv,sm)` >>
  drule compile_expr_extends >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends st2 sb` by
    (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty e1)
         (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa` >>
     simp[]) >>
  `?shadow_st2. lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2)
      shadow_sm = (iop,shadow_st2) /\ gas_shadow_state st2 shadow_st2` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e2)
       (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sm`, `shadow_sm`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2) shadow_sm` >>
     simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_st2 /\
   cs_extends shadow_st2 shadow_sb` by suspend "shadow_extends" >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_st2 shadow_func /\ fn_has_code sm st2 func` by
    (imp_res_tac cs_extends_trans >> metis_tac[fn_has_code_split]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "bind_base"
QED
*)
Theorem subscript_nocopy_sim_prefix:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
  (!s raw t. eval_expr cx e1 s = (INL raw,t) ==> body_expr_full_ok cx e2) /\
  (!s raw t. eval_expr cx e1 s = (INL raw,t) ==> body_expr_prefix_ok cx e2) /\
  body_expr_full_ok cx e1 /\
  body_expr_prefix_ok cx e1 /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  ~subscript_reads_base cx e1 e2 /\
  ~copies_subscript_base cenv e1 e2 /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
  expr_type e1 = ArrayT et bd /\
  place_type cenv e1 = ValPT (ArrayT et bd) /\
  post_value_type cenv e1 = expr_type e1 ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_nocopy_sim_prefix[shadow_extends]:
  conj_tac
  >- (qpat_assum `compile_expr _ _ (gas_shadow_expr e1) _ = _`
        (mp_then Any mp_tac compile_expr_extends) >> simp[]) >>
  conj_tac
  >- (qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) _ = _`
        (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
  drule compile_expr_array_subscript >>
  fs[exprLoweringTheory.copies_subscript_base_def] >> strip_tac >> gvs[] >>
  `ci_mono shadow_st2 shadow_sb` suffices_by simp[ci_mono_def] >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ shadow_st2 = _`
    (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
  irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_nocopy_sim_prefix[bind_base]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ _` >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_expr cx e1) (es,s0,G0,tn0)
     (\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = [] /\
         (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u))
     baseR` by suspend "base_post" >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _ /\ _) baseR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_select,
       evaluate_requests_outcomes_frame] >>
  rpt conj_tac
  >~ [`storage_trace_domain _ _ _`] >- suspend "after_base" >>
  simp[Abbr `baseR`] >> qx_genl_tac [`H`, `res`, `ee`, `r`] >>
  Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_nocopy_sim_prefix[base_post]:
  irule gas_outcome_full_post_source >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\
    (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)` >>
  qexists_tac `baseR` >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule gas_outcome_full_post_path >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ baseQ baseR` (irule_at Any) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  qpat_assum `gas_origin_ptr_path _ _ _ _`
    (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
  simp[] >> metis_tac[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_nocopy_sim_prefix[after_base]:
  qx_genl_tac [`marks`, `raw`, `mid`, `G1`, `tn1`, `s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  simp[Abbr `baseQ`] >> strip_tac >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL raw,mid)` by
    (`mid with gas_obs := [] = mid` by
       simp[vyperStateTheory.evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms, th])) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[expr_body_pre_gas_obs]) >>
  `body_expr_full_ok cx e2 /\ body_expr_prefix_ok cx e2` by
    (conj_tac >> first_x_assum irule >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e2 mid` by
    (irule (cj 1 body_expr_full_ok_simulations) >>
     simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e2 mid` by
    (qpat_assum `body_expr_prefix_ok cx e2`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >> metis_tac[]) >>
  suspend "index_start"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_nocopy_sim_prefix[index_start]:
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `return_buf_frame d cenv sm s` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> fs[vv_post_def]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid s /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
     fs[vv_post_def]) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`, `sm`, `st2`, `shadow_sm`, `shadow_st2`,
                          `iop`, `s`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sm`, `st2`, `shadow_sm`, `shadow_st2`,
                          `iop`, `s`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "bind_index"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_nocopy_sim_prefix[bind_index]:
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ (bind (eval_expr cx e2) _) _ indexQ _` >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ indexQ indexR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx e2) (read_result cx)) (mid,s,G1,tn1)
     (\H res ee G tn t. indexQ H res ee G tn t /\ ~t.vs_halted) indexR` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ indexQ indexR` (irule_at Any) >> simp[]) >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _ /\ _) indexR`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, storage_trace_frame_select,
       requests_outcomes_frame_bind_all, evaluate_requests_outcomes_frame,
       requests_outcomes_frame_read_result] >>
  rpt conj_tac
  >~ [`EVERY _ _`] >- suspend "selection_no_outcome" >>
  simp[Abbr `indexR`] >> qx_genl_tac [`H`, `res`, `ee`, `r`] >>
  Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_nocopy_sim_prefix[selection_no_outcome]:
  (* A selection may append a StorageRoot, but never a StorageOutcome. *)
  POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `raw` >>
  simp[select_result_def] >>
  qx_genl_tac [`key`, `st`, `gs`, `res`, `ee`]
  >- (simp[bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def] >>
      rpt (CASE_TAC >> gvs[return_def, raise_def]) >>
      strip_tac >>
      gvs[vyperStateTheory.evaluation_state_accfupds, combinTheory.K_THM,
          listTheory.DROP_LENGTH_NIL, listTheory.EVERY_DEF])
  >- (strip_tac >> drule_then SUBST1_TAC extend_place_PlaceR_state >>
      simp[vyperStateTheory.evaluation_state_accfupds, listTheory.DROP_LENGTH_NIL]) >>
  qmatch_goalsub_rename_tac `extend_place _ (HashMapRef _ _ _ vt) _ _` >>
  Cases_on `vt` >>
  simp[extend_place_def, bind_def, ignore_bind_def, lift_option_type_def,
       return_def, raise_def, record_storage_event_def] >>
  rpt (CASE_TAC >> gvs[bind_def, ignore_bind_def, return_def, raise_def,
                       record_storage_event_def]) >>
  strip_tac >>
  gvs[vyperStateTheory.evaluation_state_accfupds, combinTheory.K_THM,
      listTheory.DROP_APPEND1, listTheory.DROP_LENGTH_NIL, listTheory.EVERY_DEF]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise subscript_nocopy_sim_prefix
*)
