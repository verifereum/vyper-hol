(* An element of a target on the joint line: the base target's run, then
   the index's value run, then the element's own suffix (subscript_tail_full,
   proved per base kind in bodyFullTargetArray / bodyFullTargetMapping).

   TOP-LEVEL:
     subscript_tail_full -- the element suffix from the post-index endpoint
     target_subscript_sim_full -- base and index compose with a tail *)
Theory bodyFullTargetSubscript
Ancestors
  bodyFullTargetDefs gasOutcomeFullCompose gasOutcomeFull bodyFullPreds
  bodySimFull targetPlaceSimCasesBase targetPlaceSim targetPlaceSimDefs
  gasShadowCompile gasShadowCompileHelpers gasShadow gasShadowState
  gasExemptCert stmtLoweringMono exprLoweringProps fragExec freshWrites
  bodyMemoryDefs bodyPtrDefs loweringPosts exprSimHypsDefs exprSimDefs
  compileEnv exprLowering loweringStateRelDefs gasContext bodyFullShared
  vyperStorageTrace vyperStorageFootprint vyperTypeEnv vyperTypeSystem
  vyperInterpreter vyperState list pair

(* New definition (proof-internal): what the element suffix must give, from
   the endpoint after the base and the index ran, for target_sim_full of
   the subscript.  The facts are the base's and the index's own posts. *)
Definition subscript_tail_full_def:
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es <=>
    !st0 vt bvt sa sm sn sb rb iop r s0 G0 tn0 pv v
     mid1 t1 G1 tn1 mid2 t2 G2 tn2.
      type_place_target env bt = SOME bvt /\
      type_place_target env (SubscriptTarget bt e) = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (rb, sm) /\
      lower_value compile_expr cenv (expr_type e) e sm = (iop, sn) /\
      compile_get_target_ptr compile_expr cenv (SubscriptTarget bt e) sa =
        (r, sb) /\
      fn_has_code sn sb func /\ fn_inst_ids_distinct func /\
      ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
      sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      expr_sim_inv cenv cx env mid1 /\ mid1.gas_obs = [] /\
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

Theorem target_subscript_sim_full:
  body_inv tops ctx cenv cx /\
  body_base_target_full_ok cx (SubscriptTarget bt e) /\
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
  Cases_on `compile_get_target_ptr compile_expr cenv (gas_shadow_target bt)
              shadow_sa` >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa =
             (srb, shadow_sm)` >>
  qspecl_then [`compile_get_target_ptr compile_expr cenv bt`,
               `compile_get_target_ptr compile_expr cenv (gas_shadow_target bt)`,
               `sa`, `shadow_sa`, `rb`, `sm`, `srb`, `shadow_sm`] mp_tac
    (Q.GENL [`f`, `g`, `s`, `t`, `x`, `s'`, `y`, `t'`] gas_shadow_step) >>
  (impl_tac
   >- (simp[] >>
       mp_tac (MATCH_MP gas_shadow_compiles_get_target_ptr
                 (CONJUNCT1 gas_shadow_compile_expr)) >>
       disch_then (qspecl_then [`bt`, `cenv`, `T`] mp_tac) >> simp[])) >>
  strip_tac >> gvs[] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)
              shadow_sm` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sm = (siop, shadow_sn)` >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e))` by
    (irule (gas_shadow_compiles_lower_value
            |> INST [``sh:bool`` |-> ``T``] |> REWRITE_RULE []) >>
     MATCH_ACCEPT_TAC (CONJUNCT1 gas_shadow_compile_expr)) >>
  qspecl_then [`lower_value compile_expr cenv (expr_type e) e`,
               `lower_value compile_expr cenv (expr_type e) (gas_shadow_expr e)`,
               `sm`, `shadow_sm`, `iop`, `sn`, `siop`, `shadow_sn`] mp_tac
    (Q.GENL [`f`, `g`, `s`, `t`, `x`, `s'`, `y`, `t'`] gas_shadow_step) >>
  (impl_tac >- simp[]) >> strip_tac >> gvs[] >>
  `expr_type (gas_shadow_expr e) = expr_type e` by simp[gas_shadow_expr_type] >>
  qspecl_then [`compile_expr`, `cenv`, `gas_shadow_target bt`,
               `gas_shadow_expr e`, `shadow_sa`, `rb`, `shadow_sm`, `iop`,
               `shadow_sn`, `r`, `shadow_sb`] mp_tac target_subscript_compile_cut >>
  (impl_tac >- simp[compile_expr_ci_mono]) >> strip_tac >>
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
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  irule gas_outcome_full_bind_all >>
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
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
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
  `body_expr_full_ok cx e` by
    (fs[body_base_target_full_ok_def] >> first_x_assum irule >> metis_tac[]) >>
  `expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
     cenv cx (expr_type e) e mid1` by
    (fs[body_expr_full_ok_def] >> metis_tac[]) >>
  suspend "index_run"
QED

Resume target_subscript_sim_full[index_run]:
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
  >- (simp[] >> rpt conj_tac
      >- metis_tac[not_fresh_at_mono]
      >- metis_tac[not_fresh_at_mono] >>
      gen_tac >> strip_tac >>
      first_x_assum drule >> simp[target_post_def]) >>
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
  metis_tac[expr_exit_INR_retype]
QED

Resume target_subscript_sim_full[tail]:
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
  qpat_x_assum `subscript_tail_full _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [subscript_tail_full_def]) >>
  disch_then (qspecl_then [`st0`, `vt`, `bvt`, `sa`, `sm`, `sn`, `sb`, `rb`,
                           `iop`, `r`, `s0`, `G0`, `tn0`, `pv`, `v`,
                           `mid1`, `t1`, `G1`, `tn1`, `mid2`, `t2`, `G2`,
                           `tn2`] mp_tac) >>
  qunabbrev_tac `childR` >> disch_then irule >> simp[] >> rpt conj_tac
  >- (gen_tac >> strip_tac >>
      `valid_horizon cx st0 H mid1.storage_trace` by metis_tac[] >>
      qpat_x_assum `!H. valid_horizon _ _ H mid2.storage_trace ==>
                        valid_horizon _ _ H mid1.storage_trace` kall_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
        drule >>
      qpat_x_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
        drule >> simp[])
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
           (fn th => asm_simp_tac (srw_ss()) [Once bind_def, th]))) >>
  fs[target_post_def]
QED

Finalise target_subscript_sim_full
