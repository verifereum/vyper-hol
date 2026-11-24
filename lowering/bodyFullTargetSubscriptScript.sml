(* An element of a target on the joint line: the base target's run, then
   the index's value run, then the element's own suffix (subscript_tail_full,
   proved per base kind in bodyFullTargetArray / bodyFullTargetMapping).

   TOP-LEVEL:
     subscript_tail_full -- the element suffix from the post-index endpoint
     target_subscript_sim_full -- base and index compose with a tail *)
Theory bodyFullTargetSubscript
Ancestors
  bodyFullShadowBodyInv bodySim bodyInvMetadataProps targetSubscriptContinuation
  bodyFullImmSubscriptIndexPre exprSimFullBundleProps
  bodyFullTargetDefs bodyFullTargetRoots bodyFullTargetImmutableArray bodyFullTargetImmutableWrite
  bodyFullSubscriptLiveImmSelect bodySimAugPlaceLoad immutableDeployAssignFacts
  exprWordOperand exprSimSource targetSubscriptSplit gasShadowCompileStmtHelpers
  exprSimSubscriptArrayLiveImmutableView exprSimCopy vyperTypeValues vyperValue
  vyperPlaceResultTyping vyperTypeExprResult vyperTyping exprSimHyps
  vyperTypeInvariants targetSubscriptMemory tuplePlaceSourceHead loweringStateRelDefs
  gasOutcomeFullCompose gasOutcomeFull bodyFullPreds bodyFullSimProjection
  bodySimFull bodyFullIfExpReach bodyFullHashKeccakFixed
  contextRawReachable ptrDiscipline unitMemInv
  targetPlaceSimCasesBase targetPlaceSimCases targetPlaceSim targetPlaceSimDefs
  gasShadowCompile gasShadowCompileHelpers gasShadow gasShadowState
  gasExemptCert stmtLoweringMono exprLoweringProps fragExec freshWrites
  bodyMemoryDefs bodyPtrDefs loweringPosts exprSimHypsDefs exprSimDefs
  compileEnv exprLowering loweringStateRelDefs gasContext bodyFullShared
  vyperStorageTrace vyperStorageFootprint vyperTypeEnv vyperTypeSystem
  vyperInterpreter vyperState vyperAST vyperValue evalNoHalt list pair

Theorem gas_outcome_full_post_source_exit[local]:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q R /\
  (!H res ee G' tn' t. Q H res ee G' tn' t ==> Q' H res ee G' tn' t) /\
  (!H res ee gt r.
     (?st st'. source st = (res, st')) /\ R H res ee gt r ==>
     R' H res ee gt r) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0 source
    (es, s, G, tn) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def]) >>
  rewrite_tac[gas_outcome_full_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >>
      rpt conj_tac >- fs[] >- fs[] >>
      `?st st'. source st = (res, st')` by
        (qexistsl_tac
           [`es with gas_obs := gas_explicit marks s.vs_gas_readings`,
            `ee with gas_obs := []`] >>
         qpat_x_assum `!tail. source _ = _`
           (qspec_then `[]` mp_tac) >> simp[]) >>
      rpt strip_tac >> res_tac >> metis_tac[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

(* New definition (proof-internal): what the element suffix must give, from
   the endpoint after the base and the index ran, for target_sim_full of
   the subscript.  The facts are the base's and the index's own posts. *)
Definition subscript_tail_full_def:
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es <=>
    !st0 vt bvt sa sm sn sb rb iop r s0 G0 tn0 pv v base_gas index_gas
     mid1 t1 G1 tn1 mid2 t2 G2 tn2.
      type_place_target env bt = SOME bvt /\
      type_place_target env (SubscriptTarget bt e) = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
      lower_value compile_expr cenv (expr_type e) e sm = (iop, sn) /\
      compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa =
        (r, sb) /\
      fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\
      local_ptrs_reserved cenv sa /\
      sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      expr_sim_inv cenv cx env mid1 /\ mid1.gas_obs = [] /\
      eval_base_place cx bt (es with gas_obs := base_gas) =
        (INL pv, mid1) /\
      bind (eval_expr cx e) (read_result cx)
        (mid1 with gas_obs := index_gas) = (INL v, mid2) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      gas_admissible (extend_place cx pv (ValueSubscript v))
        target_res_ok mid2 /\
      storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
      ~t1.vs_halted /\ ~t2.vs_halted /\
      t1.vs_current_bb = sm.cs_current_bb /\
      t1.vs_inst_idx = LENGTH sm.cs_current_insts /\
      t2.vs_current_bb = sn.cs_current_bb /\
      t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
      alloca_history func t1 /\ alloca_history func t2 /\
      s0.vs_alloca_next <= t1.vs_alloca_next /\
      t1.vs_alloca_next <= t2.vs_alloca_next /\
      (!H. valid_horizon cx st0 H mid2.storage_trace ==>
        target_post H ctx func cenv cx es sa sm s0 mid1 pv bvt rb t1 /\
        ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
        target_ptr_ok cenv pv rb G1 tn1 t1 /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
        expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
        expr_store_bound cx (expr_type e) v iop t2 /\
        ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
        ptr_val_ok cx (post_value_type cenv e) v iop G2 tn2 t2 /\
        (~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e iop G2 t2) /\
        ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2) ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (extend_place cx pv (ValueSubscript v))
        (mid2, t2, G2, tn2)
        (\H res ee G tn t. ?pv'. res = INL pv' /\
          target_post H ctx func cenv cx es sa sb s0 ee pv' vt r t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          target_ptr_ok cenv pv' r G tn t /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt q. expr_exit res q)
End

(* The index is compiled right after the base, in both kinds of subscript. *)
Theorem ci_mono_from_eq[local]:
  f s = (x, s') ==> (!s. ci_mono s (SND (f s))) ==> ci_mono s s'
Proof
  rpt strip_tac >> first_x_assum (qspec_then `s` mp_tac) >> simp[]
QED

Theorem target_subscript_compile_cut[local]:
  !cfn ce bt e st rb sm iop sn r sb.
    (!ce ty e st. ci_mono st (SND (cfn ce ty e st))) /\
    compile_get_target_ptr cfn ce bt st = (rb, sm) /\
    lower_value cfn ce (expr_type e) e sm = (iop, sn) /\
    compile_get_target_ptr cfn ce (SubscriptTarget bt e) st = (r, sb) ==>
    ci_mono st sm /\ ci_mono sm sn /\ ci_mono sn sb
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono st sm` by metis_tac[ci_mono_compile_get_target_ptr_cfn, SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_lower_value_cfn, SND] >>
  simp[] >> PairCases_on `rb` >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [compile_get_target_ptr_def]) >>
  simp[comp_bind_def, LET_THM] >>
  Cases_on `rb2` >> TRY (rename1 `SOME pt` >> Cases_on `pt`) >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  TRY (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
         (mp_tac o MATCH_MP ci_mono_from_eq) >>
       (impl_tac
        >- (gen_tac >> irule ci_mono_compile_array_subscript >>
            simp[ci_mono_compile_ptr_load])) >>
       simp[] >> NO_TAC) >>
  qpat_x_assum `compile_mapping_subscript _ _ _ = _`
    (mp_tac o MATCH_MP ci_mono_from_eq) >>
  (impl_tac >- simp[ci_mono_compile_mapping_subscript]) >>
  qpat_x_assum `(if _ then _ else _) _ = _`
    (mp_tac o MATCH_MP ci_mono_from_eq) >>
  (impl_tac >- rw[ci_mono_compile_keccak256_key, ci_mono_comp_return]) >>
  metis_tac[ci_mono_trans]
QED

(* The same exception exits whatever the success type of the source result. *)
Theorem expr_exit_INR_retype:
  expr_exit (INR y : 'a + exception) r ==> expr_exit (INR y : 'b + exception) r
Proof
  Cases_on `y` >> Cases_on `r` >> simp[expr_exit_def] >>
  TRY (rename1 `Error er` >> Cases_on `er` >> simp[expr_exit_def])
QED

Theorem gas_shadow_compile_result[local]:
  gas_shadow_compiles f g ==>
  f s = (x,s') /\ gas_shadow_state s t ==>
  ?t'. g t = (x,t') /\ gas_shadow_state s' t'
Proof
  strip_tac >> strip_tac >>
  Cases_on `g t` >> drule_all gas_shadow_step >> simp[]
QED

Theorem target_subscript_sim_full:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt es /\
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es ==>
  target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> simp[target_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `type_place_target _ (SubscriptTarget _ _) = _`
    (strip_assume_tac o REWRITE_RULE [type_place_target_SubscriptTarget]) >>
  rename1 `type_place_target env bt = SOME bvt` >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr _ _ bt sa = (rb, sm)` >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sm` >>
  rename1 `lower_value _ _ _ e sm = (iop, sn)` >>
  qspecl_then [`compile_expr`, `cenv`, `bt`, `e`, `sa`, `rb`, `sm`, `iop`,
               `sn`, `r`, `sb`] mp_tac target_subscript_compile_cut >>
  (impl_tac >- simp[compile_expr_ci_mono]) >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (assume_tac o SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  `?shadow_sm.
     compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt) shadow_sa = (rb,shadow_sm) /\
     gas_shadow_state sm shadow_sm` by
    (irule (MATCH_MP gas_shadow_compile_result gas_shadow_stmt_get_target_ptr_env) >>
     qexists_tac `sa` >> simp[]) >>
  `?shadow_sn.
     lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
     gas_shadow_state sn shadow_sn` by
    (irule (MATCH_MP gas_shadow_compile_result gas_shadow_stmt_lower_value_env) >>
     qexists_tac `sm` >> simp[]) >>
  qpat_assum `compile_get_target_ptr _ _
    (SubscriptTarget (gas_shadow_target _) (gas_shadow_expr _)) shadow_sa = _`
    (mp_then (Pos last) mp_tac target_subscript_compile_cut) >>
  simp[compile_expr_ci_mono, gas_shadow_expr_type] >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
   sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sn /\
   cs_extends shadow_sn shadow_sb` by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sn shadow_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  suspend "base"
QED

Resume target_subscript_sim_full[base]:
  `eval_base_place cx (SubscriptTarget bt e) =
     bind (eval_base_place cx bt)
       (\pv. bind (bind (eval_expr cx e) (read_result cx))
                  (\v. extend_place cx pv (ValueSubscript v)))`
    by simp[FUN_EQ_THM, Once evaluate_def, bind_assoc] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  qpat_x_assum `target_sim_full _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [target_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `bvt`, `sa`, `sm`, `shadow_sa`,
                           `shadow_sm`, `rb`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_bind_all_path >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_base_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_extend_place] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\
                                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "index" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def]
QED

Resume target_subscript_sim_full[index]:
  qx_genl_tac [`marks`, `res`, `mid1`, `G1`, `tn1`, `t1`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace)
     mid1.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
    (?pv. res = INL pv /\ _) /\ _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qexists_tac `pv` >> simp[] >>
  `mid1 with gas_obs := [] = mid1` by
    simp[evaluation_state_component_equality] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL pv, mid1)`
    by (qpat_assum `!tail. eval_base_place _ _ _ = _`
          (qspec_then `[]` mp_tac) >> REWRITE_TAC [APPEND_NIL] >>
        qpat_assum `mid1 with gas_obs := [] = mid1` (fn th => REWRITE_TAC [th])) >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env mid1` by
    (irule eval_base_place_sim_inv >>
     qexistsl_tac [`bt`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                   `INL pv`] >> fs[target_pre_def]) >>
  `expr_body_pre cenv cx env e mid1` by
    fs[target_pre_def, target_indices_pre_def] >>
  `body_const_cells_agree [(NONE,tops)] cx env mid1` by
    (irule body_const_cells_agree_base >> goal_assum (drule_at Any) >> simp[]) >>
  `body_expr_full_ok cx e` by
    (fs[body_base_target_full_ok_def] >> first_x_assum irule >> metis_tac[]) >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cenv cx (expr_type e) e mid1` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  suspend "index_run"
QED

Resume target_subscript_sim_full[index_run]:
  `!fn inst s. frag_reachable ctx func t1 fn inst s ==>
    dalloca_fmp_headroom inst s` by
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
       gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t1,G1,tn1)`
       (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >>
     metis_tac[bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid1` by
    (simp[gas_admissible_def] >> rpt strip_tac >>
     Cases_on `res` >- simp[expr_res_ok_def] >> rename1 `INR ex` >>
     `target_res_ok (INR ex : eval_result + exception)` suffices_by
       simp[target_res_ok_def, expr_res_ok_def] >>
     qpat_x_assum `gas_admissible (bind (eval_base_place _ _) _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs`
                   mp_tac) >>
     qpat_assum `!tail. eval_base_place _ _ _ = _`
       (qspec_then `gs` assume_tac) >>
     simp[Once bind_def] >>
     `mid1 with gas_obs := gs = mid1 with gas_obs := gs` by simp[] >>
     simp[Once bind_def] >> gvs[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d cenv sm t1` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> fs[target_post_def]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sm`, `sn`, `shadow_sm`, `shadow_sn`, `iop`,
                           `t1`, `G1`, `tn1`] mp_tac) >>
  impl_tac
  >- (asm_rewrite_tac[] >> rpt conj_tac
      >- metis_tac[not_fresh_at_mono]
      >- metis_tac[not_fresh_at_mono] >>
      gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
        (?pv'. INL pv = INL pv' /\ _) /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      fs[target_post_def]) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) _) _ idxQ idxR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_extend_place] >>
  qexists_tac `\H res ee G tn t. idxQ H res ee G tn t /\ ~t.vs_halted /\
                                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "tail" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
    (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `idxR`, Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >>
  conj_tac
  >- (qpat_x_assum `expr_exit (INR _) _`
        (MATCH_ACCEPT_TAC o MATCH_MP expr_exit_INR_retype)) >>
  fs[halt_exit_def]
QED

Resume target_subscript_sim_full[tail]:
  `post_value_type cenv e = expr_type e` by
    (Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
     >- (gvs[] >> rename1 `Call ity (IntCall fid) args drv` >>
         PairCases_on `fid` >> fs[well_typed_expr_def, expr_type_def] >>
         qpat_assum `well_formed_type env.type_defs ity` mp_tac >>
         qpat_assum `subscript_vtype bvt ity = SOME vt` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         `is_int_type ity \/ hashmap_key_type ity` by
           (Cases_on `bvt`
            >- (rename1 `Type bty` >> Cases_on `bty` >>
                gvs[subscript_vtype_def, AllCaseEqs()]) >>
            gvs[subscript_vtype_def, AllCaseEqs()]) >>
         Cases_on `ity` >>
         gvs[is_int_type_def, hashmap_key_type_def, post_value_type_def,
             is_word_type_def, is_bytestring_type_def] >>
         rename1 `BaseT key` >> Cases_on `key` >>
         gvs[is_int_type_def, hashmap_key_type_def, post_value_type_def,
             is_word_type_def, is_bytestring_type_def] >>
         rename1 `BytesT bd` >> Cases_on `bd` >>
         gvs[is_word_type_def, is_bytestring_type_def, well_formed_type_def,
             evaluate_type_def, AllCaseEqs()]) >>
     irule post_value_type_not_int_call >> metis_tac[]) >>
  qx_genl_tac [`marks2`, `res2`, `mid2`, `G2`, `tn2`, `t2`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `idxQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
     mid2.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res2 = INL _` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  `mid2 with gas_obs := [] = mid2` by
    simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
     (mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings) =
     (INL v, mid2)`
    by (qpat_assum `!tail. bind _ _ _ = _`
          (qspec_then `[]` mp_tac) >> REWRITE_TAC [APPEND_NIL] >>
        qpat_assum `mid2 with gas_obs := [] = mid2` (fn th => REWRITE_TAC [th])) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       valid_horizon cx st0 H mid1.storage_trace` by
    (rpt strip_tac >>
     qspecl_then [`bind (eval_expr cx e) (read_result cx)`,
                  `mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings`,
                  `INL v`, `mid2`]
       mp_tac (Q.GENL [`f`, `st`, `res`, `st'`] valid_horizon_frame) >>
     simp[] >> disch_then irule >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >>
     simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  qpat_assum `post_value_type cenv e = expr_type e`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> assume_tac th) >>
  qpat_x_assum `subscript_tail_full _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [subscript_tail_full_def]) >>
  disch_then (qspecl_then [`st0`, `vt`, `bvt`, `sa`, `sm`, `sn`, `sb`, `rb`,
                           `iop`, `r`, `s0`, `G0`, `tn0`, `pv`, `v`,
                           `gas_explicit marks s0.vs_gas_readings`,
                           `gas_explicit marks2 t1.vs_gas_readings`,
                           `mid1`, `t1`, `G1`, `tn1`, `mid2`, `t2`, `G2`,
                           `tn2`] mp_tac) >>
  qunabbrev_tac `childR` >>
  disch_then assume_tac >>
  irule gas_outcome_full_post_source_exit >>
  qpat_x_assum `_ ==> gas_outcome_full _ _ _ _ (extend_place _ _ _) _ _ _`
    (irule_at Any) >>
  BETA_TAC >> simp[] >> rpt conj_tac
  >~ [`gas_admissible (extend_place _ _ _) _ _`]
  >- (simp[gas_admissible_def] >> rpt strip_tac >>
      qpat_x_assum `gas_admissible (bind (eval_base_place _ _) _) _ _`
        (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
      disch_then (qspecl_then
        [`gas_explicit marks s0.vs_gas_readings ++
          (gas_explicit marks2 t1.vs_gas_readings ++ gs)`, `res`, `ee`]
        mp_tac) >>
      disch_then (fn th => match_mp_tac th) >>
      qpat_assum `!tail. bind _ _ _ = _`
        (qspec_then `gs` (fn th =>
           `bind (bind (eval_expr cx e) (read_result cx))
              (\v. extend_place cx pv (ValueSubscript v))
              (mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ gs) =
            (res, ee)` by asm_simp_tac (srw_ss()) [Once bind_def, th])) >>
      qpat_assum `!tail. eval_base_place _ _ _ = _`
        (qspec_then `gas_explicit marks2 t1.vs_gas_readings ++ gs`
           (fn th => asm_simp_tac (srw_ss()) [Once bind_def, th])))
  >- (gen_tac >> strip_tac >>
      `valid_horizon cx st0 H mid1.storage_trace` by metis_tac[] >>
      qpat_x_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
                        valid_horizon _ _ H mid1.storage_trace` kall_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
        (?pv'. INL pv = INL pv' /\ _) /\ _`
        drule >>
      qpat_x_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
        drule >> simp[])
  >- (rpt gen_tac >> disch_then (qx_choose_then `p` strip_assume_tac) >>
      qexists_tac `p` >> simp[] >>
      fs[target_post_def, expr_post_def] >>
      drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  rpt gen_tac >> strip_tac >>
  `res <> INR HaltException` by
    (disch_then (fn eq =>
       qpat_assum `extend_place cx pv (ValueSubscript v) _ = _`
         (mp_tac o REWRITE_RULE [eq])) >>
     simp[extend_place_nh]) >>
  `!u. expr_exit res (Halt u) ==> res = INR HaltException` by
    (POP_ASSUM_LIST (K all_tac) >>
     gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
     Cases_on `y` >> simp[expr_exit_def]) >>
  simp[halt_exit_def] >>
  metis_tac[]
QED

Finalise target_subscript_sim_full


Theorem immutable_target_index_word[local]:
  is_int_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  expr_post H ctx func cenv cx e es sm sn t1 mid2 v iop t2 ==>
  ?i iw. v = IntV i /\ eval_operand iop t2 = SOME iw /\
         i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw))
Proof
  strip_tac >>
  Cases_on `expr_type e` >> gvs[vyperTypeSystemTheory.is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[vyperTypeSystemTheory.is_int_type_def,
      vyperValueTheory.evaluate_type_def, vyperTypingTheory.value_has_type_def,
      vyperTypeSystemTheory.well_formed_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  fs[loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_rel_def,
     vyperValueTheory.evaluate_type_def, AllCaseEqs(),
     compileEnvTheory.is_word_type_def,
     valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def,post_value_type_def] >>
  mp_tac exprSimArithTheory.math_val_i2w >>
  disch_then (qspec_then `expr_type e` (qspec_then `i` mp_tac)) >>
  gvs[arithmeticPropsTheory.math_val_def, compileEnvTheory.is_signed_type_def,
      compileEnvTheory.type_bits_def, vyperValueTheory.within_int_bound_def]
QED


Theorem immutable_target_operand_frame[local]:
  (!x. arg = Var x ==> not_fresh_at sm x) /\
  (!label. arg <> Label label) /\
  eval_operand arg t1 = SOME w /\ op_taint tn1 arg = {} /\ op_prov G1 arg = NONE /\
  sm.cs_next_var <= sn.cs_next_var /\
  (!x w. not_fresh_at sm x /\ lookup_var x t1 = SOME w ==>
    lookup_var x t2 = SOME w) /\
  ghost_kept_at lo cenv es sm G1 tn1 t1 G2 tn2 ==>
  copy_old_operand sn arg /\ eval_operand arg t2 = SOME w /\
  op_taint tn2 arg = {} /\ op_prov G2 arg = NONE
Proof
  strip_tac >>
  conj_tac >- (rw[copy_old_operand_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  conj_tac >-
    (match_mp_tac (Q.SPECL [`arg`,`sm`,`t1`,`t2`,`w`] exprBopSimPropsTheory.eval_operand_frame) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `arg` >> fs[ghost_kept_at_def,op_taint_def,op_prov_def] >>
  metis_tac[]
QED

Theorem immutable_target_extend_state[local]:
  SND (bind (extend_place cx (PlaceR p) sub) get_place es) = es
Proof
  Cases_on `extend_place cx (PlaceR p) sub es` >>
  drule_then SUBST_ALL_TAC vyperPlaceFramesTheory.extend_place_PlaceR_state >>
  Cases_on `q` >> simp[bind_def] >>
  Cases_on `x` >> simp[get_place_def,return_def,raise_def]
QED

Theorem immutable_target_subscript_sim_full:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env (SubscriptTarget bt e) /\
  cx.in_deploy /\ immutable_root cx bt /\ ~cx_const_name cx (NONE,id) /\
  target_root bt = TopLevelNameTarget (NONE,id) /\
  imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt es ==>
  imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env (SubscriptTarget bt e) es
Proof
  strip_tac >> simp[imm_target_place_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_assum `type_place_target _ (SubscriptTarget _ _) = _`
    (strip_assume_tac o REWRITE_RULE [type_place_target_SubscriptTarget]) >>
  rename1 `type_place_target _ bt = SOME child_vt` >>
  qspecl_then [`bt`,`tops`,`ctx`,`cenv`,`cx`,`env`,`es`,`child_vt`] mp_tac
    immutable_target_place_type >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `bty` strip_assume_tac) >> gvs[] >>
  `?et bd. bty = ArrayT et bd` by
    (Cases_on `bty` >> fs[subscript_vtype_def]) >> gvs[] >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr _ _ bt sa = (rb, sm)` >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sm` >>
  rename1 `lower_value _ _ _ e sm = (iop, sn)` >>
  qspecl_then [`compile_expr`, `cenv`, `bt`, `e`, `sa`, `rb`, `sm`, `iop`,
               `sn`, `r`, `sb`] mp_tac target_subscript_compile_cut >>
  (impl_tac >- simp[compile_expr_ci_mono]) >> strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (assume_tac o SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  `?shadow_sm.
     compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt) shadow_sa = (rb,shadow_sm) /\
     gas_shadow_state sm shadow_sm` by
    (irule (MATCH_MP gas_shadow_compile_result gas_shadow_stmt_get_target_ptr_env) >>
     qexists_tac `sa` >> simp[]) >>
  `?shadow_sn.
     lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e) shadow_sm = (iop,shadow_sn) /\
     gas_shadow_state sn shadow_sn` by
    (irule (MATCH_MP gas_shadow_compile_result gas_shadow_stmt_lower_value_env) >>
     qexists_tac `sm` >> simp[]) >>
  qpat_assum `compile_get_target_ptr _ _
    (SubscriptTarget (gas_shadow_target _) (gas_shadow_expr _)) shadow_sa = _`
    (mp_then (Pos last) mp_tac target_subscript_compile_cut) >>
  simp[compile_expr_ci_mono, gas_shadow_expr_type] >> strip_tac >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn sb /\
   sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sn /\
   cs_extends shadow_sn shadow_sb` by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code sm sn func /\ fn_has_code sn sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sn shadow_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  suspend "base"
QED

Resume immutable_target_subscript_sim_full[base]:
  drule_then (fn th =>
    qpat_assum `gas_admissible (eval_target_place _ (SubscriptTarget _ _)) _ _`
      (assume_tac o REWRITE_RULE [th,GSYM bind_assoc]) >>
    REWRITE_TAC[th,GSYM bind_assoc]) immutable_target_subscript_source >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_place_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_place_res_ok_def]) >>
  qpat_x_assum `imm_target_place_sim_full _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [imm_target_place_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `ArrayT et bd`, `sa`, `sm`, `shadow_sa`,
                           `shadow_sm`, `rb`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_bind_all_path >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> simp[])
  >~ [`storage_trace_frame (eval_target_place _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_bind,storage_trace_frame_get_place,
           storage_trace_frame_extend_place] >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\
                                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "index" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def]
QED

Resume immutable_target_subscript_sim_full[index]:
  qx_genl_tac [`marks`, `res`, `mid1`, `G1`, `tn1`, `t1`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace)
     mid1.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
    (?id path. res = INL (ImmutablePlace NONE id path) /\ _) /\ _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[] >>
  qabbrev_tac `p = ImmutablePlace NONE id path` >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sm,sn,shadow_sm,shadow_sn)` by
    simp[expr_sim_full_code_def] >>
  `IS_SOME (type_place_target env bt)` by simp[] >>
  `!H. valid_horizon cx st0 H mid1.storage_trace ==>
    imm_target_post H ctx func cenv cx es sa sm s0 mid1 id path (ArrayT et bd) rb t1 /\
    t1.vs_current_bb = sm.cs_current_bb /\ t1.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t1) /\
    s0.vs_alloca_next <= t1.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid1 G1 tn1 t1 /\
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) marks (OK t1,G1,tn1)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
       imm_target_post H ctx func cenv cx es sa sm s0 mid1 id path _ rb t1 /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> gas_origin_ptr_path _ _ _ _`
       (drule_then assume_tac) >> simp[]) >>
  `eval_base_place cx bt (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL (PlaceR p),mid1) /\
    body_const_cells_agree [(NONE,tops)] cx env mid1 /\
    expr_sim_inv cenv cx env mid1 /\ expr_body_pre cenv cx env e mid1 /\
    body_expr_full_ok cx e /\
    expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e mid1 (st0,sm,sn,shadow_sm,shadow_sn,iop,t1,G1,tn1)` by
    (simp[Abbr `p`] >> irule immutable_subscript_index_pre >>
     simp[] >> metis_tac[]) >>
  `mid1 with gas_obs := [] = mid1` by simp[evaluation_state_component_equality] >>
  `eval_target_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL p, mid1)` by
    (qpat_assum `!tail. eval_target_place _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [APPEND_NIL])) >>
     qpat_assum `mid1 with gas_obs := [] = mid1` (fn th => rewrite_tac[th]) >>
     simp[Abbr `p`]) >>
  `target_indices_pre cenv cx env bt` by fs[target_indices_pre_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e mid1` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  suspend "index_run"
QED

Resume immutable_target_subscript_sim_full[index_run]:
  qpat_x_assum `expr_sim_full _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_via_bundle]) >>
  qpat_x_assum `!st0 sa sb sha shb op s0 G0 tn0. expr_sim_full_hypotheses _ _ _ _ _ _ _ ==> _`
    (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,`iop`,`t1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o REWRITE_RULE [expr_sim_full_post_def,
      expr_sim_full_endpoint_def]) >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (bind (eval_expr cx e) _) _ idxQ idxR` >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_bind,storage_trace_frame_get_place,
           storage_trace_frame_extend_place] >>
  qexists_tac `\H res ee G tn t. idxQ H res ee G tn t /\ ~t.vs_halted /\
                                 ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "tail" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
    (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `idxR`, Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >>
  conj_tac
  >- (qpat_x_assum `expr_exit (INR _) _`
        (MATCH_ACCEPT_TAC o MATCH_MP expr_exit_INR_retype)) >>
  fs[halt_exit_def]
QED

Resume immutable_target_subscript_sim_full[tail]:
  qx_genl_tac [`marks2`,`res2`,`mid2`,`G2`,`tn2`,`t2`] >>
  BETA_TAC >> strip_tac >> disj1_tac >>
  qunabbrev_tac `idxQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
      mid2.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> (?v. res2 = INL v /\ _) /\ _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res2 = INL _` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >>
  `mid2 with gas_obs := [] = mid2` by
    simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
     (mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings) =
     (INL v,mid2)` by
    (qpat_assum `!tail. bind _ _ _ = _`
      (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     qpat_assum `mid2 with gas_obs := [] = mid2` (fn th => rewrite_tac[th]) >>
     simp[]) >>
  qabbrev_tac `ix = mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings` >>
  `expr_body_pre cenv cx env e ix` by simp[Abbr `ix`,expr_body_pre_gas_obs] >>
  `is_int_type (expr_type e) /\ ty = et` by
    (qpat_assum `subscript_vtype (Type (ArrayT et bd)) (expr_type e) = SOME (Type ty)` mp_tac >>
     simp_tac (srw_ss()) [subscript_vtype_def,AllCaseEqs()]) >>
  `is_word_type (expr_type e)` by
    (Cases_on `expr_type e` >> gvs[is_int_type_def] >>
     rename1 `is_word_type (BaseT bt')` >> Cases_on `bt'` >>
     gvs[is_int_type_def,is_word_type_def]) >>
  drule_all_then strip_assume_tac
    (SIMP_RULE (srw_ss() ++ ETA_ss) [] expr_body_pre_word_type_result) >>
  qpat_assum `!w. INL v = INL w ==> _`
    (qspec_then `v` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  gvs[] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
    expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\ _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` (drule_then strip_assume_tac)) >>
  `?i iw. v = IntV i /\ eval_operand iop t2 = SOME iw /\
     i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw))` by
    (irule (INST_TYPE [alpha |-> ``:256``] immutable_target_index_word) >> simp[] >>
     qexistsl [`storage_trace_horizon mid2.storage_trace`,`cenv`,`ctx`,`cx`,
       `mid1`,`func`,`mid2`,`sm`,`sn`,`t1`,`tyv`] >> simp[]) >>
  gvs[] >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
     valid_horizon cx st0 H mid1.storage_trace` by
    (rpt strip_tac >>
     qspecl_then [`bind (eval_expr cx e) (read_result cx)`,
       `mid1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings`,
       `INL (IntV (if is_signed_type (expr_type e) then w2i iw else &(w2n iw)))`,`mid2`]
       mp_tac (Q.GENL [`f`,`st`,`res`,`st'`] valid_horizon_frame) >>
     asm_rewrite_tac[] >>
     simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H mid1.storage_trace ==>
     valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qspecl_then [`eval_target_place cx bt`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`INL p`,`mid1`]
       mp_tac (Q.GENL [`f`,`st`,`res`,`st'`] valid_horizon_frame) >>
     asm_rewrite_tac[] >> simp[evaluate_storage_trace_frame]) >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==>
    imm_target_post H ctx func cenv cx es sa sm s0 mid1 id path _ rb t1 /\ _`
    (qspec_then `storage_trace_horizon mid1.storage_trace` (drule_then
      (CONJUNCTS_THEN2 (strip_assume_tac o REWRITE_RULE[imm_target_post_def])
        assume_tac))) >>
  `IS_SOME (type_place_target env bt)` by simp[] >>
  drule_all_then (qx_choosel_then [`root`,`root_ty`] strip_assume_tac)
    typed_immutable_target_root >>
  `root = id` by
    (qpat_assum `target_root bt = TopLevelNameTarget (NONE,root)` mp_tac >>
     qpat_assum `target_root bt = TopLevelNameTarget (NONE,id)` (fn th => simp[NoAsms,th])) >>
  qpat_x_assum `root = id` SUBST_ALL_TAC >>
  `cenv.ce_module = NONE /\ evaluate_type (get_tenv cx) root_ty = SOME itv` by
    (qunabbrev_tac `p` >>
     drule_all_then strip_assume_tac immutable_target_write_root >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `off + type_memory_size itv < dimword (:256)` by
    (drule_all_then (strip_assume_tac o Q.SPEC `compile_expr`) immutable_assign_target_layout >>
     `off' = off` by
       (qpat_assum `FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off')` mp_tac >>
        qpat_assum `FLOOKUP cenv.ce_module_vars (NONE,id) = SOME (ImmutableLoc off)`
          (fn th => simp[NoAsms,th])) >>
     qpat_x_assum `off' = off` SUBST_ALL_TAC >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `?raw. eval_expr cx e ix = (INL raw,mid2)` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx) ix = (INL _,mid2)`
       (mp_tac o MATCH_MP (SIMP_RULE (srw_ss() ++ ETA_ss) [] eval_expr_read_INL)) >>
     disch_then (qx_choosel_then [`raw`,`mid`] strip_assume_tac) >>
     drule_then (SUBST_ALL_TAC o GSYM) read_result_state >>
     qexists_tac `raw` >> first_assum ACCEPT_TAC) >>
  rename1 `evaluate_subscripts itv iv path = INL base_v` >>

  `~target_subscript_overlap cenv bt e` by
    (qpat_assum `target_indices_pre _ _ _ (SubscriptTarget bt e)` mp_tac >>
     simp[NoAsms,target_indices_pre_def]) >>
  `expr_sim_inv cenv cx env mid2 /\
    ?current a. FLOOKUP (case ALOOKUP mid2.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables NONE imms) id =
      SOME (itv,current) /\ evaluate_subscripts itv current path = INL a` by
    (match_mp_tac (Q.INST [`es` |-> `ix`,`idx` |-> `e`,`ee` |-> `mid2`,
       `res` |-> `INL raw`,`v` |-> `base_v`,`old` |-> `iv`,
       `root_ty` |-> `root_ty`,`path` |-> `path`] immutable_target_path_after_index) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (ix = _)` (fn th =>
       simp[NoAsms,REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> first_assum (drule_all_then ACCEPT_TAC)) >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\ ptv = ArrayTV etv bd` by
    (qpat_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[NoAsms,evaluate_type_def] >>
     Cases_on `evaluate_type (get_tenv cx) et` >> simp[NoAsms] >>
     IF_CASES_TAC >> simp[NoAsms]) >>
  qpat_x_assum `ptv = ArrayTV etv bd` SUBST_ALL_TAC >>
  `value_has_type (ArrayTV etv bd) a` by
    (qspecl_then [`cenv`,`cx`,`env`,`mid2`,`NONE`,`id`,`path`,
      `itv`,`current`,`k`,`ArrayTV etv bd`,`a`] mp_tac imm_place_at_value_type >>
     simp[]) >>
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `evaluate_subscripts itv current path = INL (ArrayV av)` >>
  `target_subscript_suffix cenv e rb iop sn = (r,sb)` by
    (qpat_assum `compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa = (r,sb)`
       (mp_tac o MATCH_MP target_subscript_compile_decompose) >>
     simp[] >> TRY (disch_then ACCEPT_TAC)) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> qexistsl [`cx`,`env`,`mid2`] >> simp[]) >>
  `rb = (FST rb,SOME LocCode,SOME (ValPT (ArrayT et bd)))` by
    (PairCases_on `rb` >> gvs[]) >>
  qpat_assum `rb = _` (fn th =>
    qpat_x_assum `target_subscript_suffix cenv e rb iop sn = (r,sb)`
      (mp_tac o ONCE_REWRITE_RULE[th])) >>
  rewrite_tac[target_subscript_suffix_array,elem_size_in_location_def,word_scale_def] >>
  disch_then (qx_choose_then `dst` strip_assume_tac) >>
  qpat_x_assum `r = (_,_,_)` SUBST_ALL_TAC >>
  suspend "run_tail"
QED

Resume immutable_target_subscript_sim_full[run_tail]:
  `!l. FST rb <> Label l` by drule_all_then ACCEPT_TAC target_subscript_typed_base_not_label >>
  `sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sn` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by metis_tac[not_fresh_at_mono] >>
  `copy_old_operand sn (FST rb) /\ eval_operand (FST rb) t2 = SOME (n2w (off+k)) /\
    op_taint tn2 (FST rb) = {} /\ op_prov G2 (FST rb) = NONE` by
    (qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
       expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 _ iop t2 /\ _`
       (qspec_then `storage_trace_horizon mid2.storage_trace`
         (drule_then (CONJUNCTS_THEN2
           (strip_assume_tac o REWRITE_RULE[expr_post_def]) assume_tac))) >>
     qpat_assum `target_ptr_ok cenv (PlaceR p) rb G1 tn1 t1`
       (strip_assume_tac o REWRITE_RULE[target_ptr_ok_def]) >>
     match_mp_tac (Q.INST [`arg` |-> `FST rb`,`sm` |-> `sm`,
       `t1` |-> `t1`,`tn1` |-> `tn1`,`G1` |-> `G1`,`lo` |-> `lo`,
       `cenv` |-> `cenv`,`es` |-> `mid1`] immutable_target_operand_frame) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[arithmeticTheory.ADD_COMM]) >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `copy_old_operand sn iop /\ (!l. iop <> Label l)` by
    (drule_all_then strip_assume_tac expr_body_pre_lower_value_word_shape >>
     rewrite_tac[copy_old_operand_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `op_taint tn2 iop = {} /\ op_prov G2 iop = NONE` by
    (qpat_assum `is_word_type (expr_type e)` (fn word =>
      qpat_assum `ptr_val_ok cx (expr_type e) _ iop G2 tn2 t2`
        (ACCEPT_TAC o SIMP_RULE std_ss [ptr_val_ok_def,word]))) >>
  `MAP FDOM es.scopes = MAP FDOM mid1.scopes` by
    (drule_then mp_tac vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom >>
     simp[]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid2 t2 /\ storage_well_formed_on cx mid2 (FST H) /\
    wb_frame cenv es mid2 sa s0 t2 /\ ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2 /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by suspend "frames" >>
  `sa.cs_next_var <= sn.cs_next_var /\ s0.vs_alloca_next <= t2.vs_alloca_next` by
    decide_tac >>
  `compile_array_subscript (FST rb) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0) 32 (type_memory_size etv)
      (is_signed_type (expr_type e))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sn = (dst,sb)` by
    (qpat_assum `type_memory_bytes cenv et = type_memory_size etv` (fn bytes =>
       qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = (dst,sb)`
         (ACCEPT_TAC o SIMP_RULE std_ss [is_slot_addressed_def,bytes]))) >>
  qunabbrev_tac `p` >>
  irule gas_outcome_full_post_source >>
  irule_at Any immutable_target_array_tail >>
  simp[Abbr `childR`] >>
  qexistsl [`tops`,`tn0`,`sn`,`is_signed_type (expr_type e)`,`sb`,`sa`,
    `s0`,`off`,`iw`,`iop`,`et`,`es`,`env`,`dst`,`d`,`cenv`,
    `FST rb`,`G0`] >>
  simp[arithmeticTheory.ADD_COMM] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "tail_post"
QED

Resume immutable_target_subscript_sim_full[tail_post]:
  conj_tac >-
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid2 t2 /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[target_root_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `?xs. !tail. _ = (_, ee with gas_obs := tail)`
    (qx_choose_then `xs` assume_tac) >>
  `ee.immutables = mid2.immutables` by
    (qpat_assum `!tail. _ = (_, ee with gas_obs := tail)`
       (qspec_then `[]` (mp_tac o AP_TERM ``SND : (place + exception) # evaluation_state -> evaluation_state``)) >>
     simp[immutable_target_extend_state] >>
     disch_then (mp_tac o AP_TERM ``(\s:evaluation_state. s.immutables)``) >> simp[]) >>
  Cases_on `bd`
  >- (fs[allocLimitsTheory.target_through_dynarray_def,imm_target_post_def] >>
      qpat_x_assum `itv' = itv` SUBST_ALL_TAC >>
      match_mp_tac (Q.INST [`k` |-> `k`,`k'` |-> `k'`,
        `tv` |-> `ArrayTV etv (Fixed n)`,`tv'` |-> `ptv`]
        immutable_target_fixed_snoc) >> simp[]) >>
  qpat_x_assum `~target_through_dynarray cenv (SubscriptTarget bt e)` mp_tac >>
  qpat_assum `target_place_type cenv bt = SOME (ValPT (ArrayT et (Dynamic n)))`
    (fn ty => simp[NoAsms,Once allocLimitsTheory.target_through_dynarray_def,ty])
QED

Resume immutable_target_subscript_sim_full[frames]:
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H mid1.storage_trace` by
    (first_assum (drule_then ACCEPT_TAC)) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (first_assum (drule_then ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
    expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 _ iop t2 /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `wb_frame cenv es mid1 sa s0 t1` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv mid1 mid2 sm t1 t2` by
    drule_then ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame >>
  `stmt_state_rel H ctx func cenv cx mid2 t2 /\
    storage_well_formed_on cx mid2 (FST H)` by
    (qpat_assum `expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 _ iop t2`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es mid2 sa s0 t2` by
    (match_mp_tac (Q.INST [`H` |-> `H`]
       (Q.SPECL [`func`,`cenv`,`cx`,`es`,`s0`,`sa`,`mid1`,`mid2`,
          `sm`,`t1`,`t2`,`ctx`]
          (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  match_mp_tac (Q.SPECL [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,
      `G1`,`tn1`,`mid1`,`sm`,`G2`,`tn2`,`t1`,`H`,`ctx`,`func`,`cx`,`mid1`]
    (INST_TYPE [beta |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans)) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise immutable_target_subscript_sim_full
