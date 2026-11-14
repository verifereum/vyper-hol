(* Joint evaluation of the scalar arguments of ECRecover. *)
Theory bodyFullBuiltinPrecompileRecoveryArgs
Ancestors
  bodyFullPreds bodySimFull bodyFullExprGeneric gasOutcomeFullCompose
  exprSimPrecompiles exprSimWordArgs wordArgsPtr exprSimSource exprSimHyps
  exprLoweringProps gasShadowCompileStmtHelpers gasShadowState
  bodyPtrDefs loweringPosts vyperStorageTrace vyperStorageFootprint
  vyperEvalExprPreservesScopesDom fragGasOriginPtr fragGasOrigin
  fragGasPath fragGasMode fragExec gasExemptCert gasSummaryCompose
  vyperInterpreter vyperState venomState list finite_map pred_set

(* Original application anchors typing; the suffix post uses its own start. *)
Theorem ecrecover_args_suffix_full:
  !todo DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty
    ann args done entry es st0 sa sm shadow_sa shadow_sm xs s0 G0 tn0.
    expr_body_pre cenv cx env (Builtin ann ECRecover args) entry /\
    args = done ++ todo /\ body_exprs_full_ok cx todo /\
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    lower_word_args cenv (\e. ty) todo sa = (xs,sm) /\
    lower_word_args cenv (\e. ty) (MAP gas_shadow_expr todo) shadow_sa =
      (xs,shadow_sm) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx todo) (es,s0,G0,tn0)
      (\H rr mid G tn t. ?vs. rr = INL vs /\
        typed_args_post H ctx func cenv cx es sa s0 mid todo xs vs t /\
        t.vs_current_bb = sm.cs_current_bb /\
        t.vs_inst_idx = LENGTH sm.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx mid G tn t /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H rr mid gt r. wb_args_exit rr r)
Proof
  Induct
  >- (simp[lower_word_args_nil] >> rpt strip_tac >>
      irule gas_outcome_full_pure >> conj_tac
      >- (qexistsl_tac [`G0`, `es`, `INL []`, `s0`, `tn0`] >>
          simp[eval_exprs_nil] >> rpt strip_tac >>
          first_x_assum drule >> strip_tac >>
          simp[cj 1 gas_origin_ptr_path_rules, typed_args_post_def,
               wb_frame_refl, ghost_kept_at_def]
          >- (qsuff_tac `storage_well_formed_on cx (es with gas_obs := []) (FST H) =
                         storage_well_formed_on cx es (FST H)`
              >- simp[] >> irule storage_well_formed_on_backends >> simp[]) >>
          qpat_x_assum `ghost_inv_at _ _ _ _ _ _ _ _ _` mp_tac >>
          rewrite_tac[ghost_inv_at_def] >> strip_tac >>
          simp[] >> first_assum ACCEPT_TAC) >> simp[])
  >> rpt gen_tac >> strip_tac >>
  rename1 `body_exprs_full_ok cx (e::rest)` >>
  `MEM e args` by simp[] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e`, `es`] mp_tac) >> simp[]) >>
  `is_word_type (expr_type e)` by
    (drule ecrecover_pre_types >> simp[EVERY_MEM] >> metis_tac[]) >>
  gvs[lower_word_args_cons, MAP] >>
  `gas_shadow_state s1 s1'` by
    (mp_tac gas_shadow_stmt_lower_value >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    metis_tac[expr_body_pre_lower_value_word_shape] >>
  `wb_args_shape cenv (\e. ty) rest` by
    (simp[wb_args_shape_def] >> rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e' es` by
       (drule expr_body_pre_builtin_arg >>
        disch_then (qspecl_then [`e'`, `es`] mp_tac) >> simp[]) >>
     `is_word_type (expr_type e')` by
       (drule ecrecover_pre_types >> simp[EVERY_MEM] >> metis_tac[]) >>
     metis_tac[expr_body_pre_lower_value_word_shape]) >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sm func` by
    metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
  `cs_extends shadow_sa s1'` by
    (mp_tac (Q.SPECL [`cenv`, `ty`, `gas_shadow_expr e`, `shadow_sa`]
      ci_mono_lower_value_compile_expr) >> simp[ci_mono_def]) >>
  `!a b zs. lower_word_args cenv (\e. ty) (MAP gas_shadow_expr rest) a = (zs,b) ==>
      cs_extends a b` by
    (POP_ASSUM_LIST (K all_tac) >> Induct_on `rest` >>
     simp[lower_word_args_nil, compileEnvTheory.cs_extends_refl] >>
     rpt strip_tac >> gvs[lower_word_args_cons] >>
     metis_tac[ci_mono_lower_value_compile_expr, ci_mono_def, pairTheory.SND,
               compileEnvTheory.cs_extends_trans]) >>
  `fn_has_code shadow_sa s1' shadow_func /\
   fn_has_code s1' shadow_sm shadow_func` by
    metis_tac[fn_has_code_mid, compileEnvTheory.cs_extends_refl] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_x_assum `body_exprs_full_ok _ _` mp_tac >>
     simp[body_exprs_full_ok_def] >> strip_tac >>
     qpat_x_assum `body_expr_full_ok _ _` mp_tac >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `s1'`, `x`,
    `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_return])
  >> qexists_tac `(\H rr ee G tn u. headQ H rr ee G tn u /\ ~u.vs_halted)` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      goal_assum (drule_at Any) >> conj_tac
      >- simp[] >>
      simp[Abbr `headR`, wb_args_exit_def] >>
      Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `?v. res = INL v` by
    (qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[GSYM storage_trace_domain_def, Abbr `headQ`] >>
     BETA_TAC >> strip_tac >> goal_assum (drule_at Any)) >>
  pop_assum strip_assume_tac >> gvs[] >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >>
     `expr_body_pre cenv cx env e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qpat_x_assum `expr_body_pre _ _ _ _ (_ with gas_obs := _)` mp_tac >>
     qpat_x_assum `bind _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     imp_res_tac expr_body_pre_eval >> fs[SF ETA_ss] >>
     qpat_x_assum `!res es'. _ ==> expr_sim_inv _ _ _ _`
       (qspecl_then [`INL v`, `mid with gas_obs := []`] mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx e es sa s1 s0 mid v x t /\
      t.vs_current_bb = s1.cs_current_bb /\
      t.vs_inst_idx = LENGTH s1.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ ~t.vs_halted` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     simp[Abbr `headQ`] >> rpt strip_tac >> simp[]) >>
  `t.vs_current_bb = s1.cs_current_bb /\
   t.vs_inst_idx = LENGTH s1.cs_current_insts /\
   alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted` by
    (qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[GSYM storage_trace_domain_def] >> rpt strip_tac >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d cenv s1 t` by
    (qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[GSYM storage_trace_domain_def] >> strip_tac >>
     gvs[expr_post_def] >> Cases_on `d` >>
     fs[return_buf_frame_def] >> PairCases_on `x'` >>
     fs[return_buf_frame_def] >>
     metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx rest) (mid,t,G1,tn1)
      (\H rr fin G tn u. ?vs. rr = INL vs /\
        typed_args_post H ctx func cenv cx mid s1 t fin rest ys vs u /\
        u.vs_current_bb = sm.cs_current_bb /\
        u.vs_inst_idx = LENGTH sm.cs_current_insts /\
        alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx fin G tn u /\
        ghost_kept_at lo cenv mid s1 G1 tn1 t G tn)
      (\H rr fin gt r. wb_args_exit rr r)` by
    (first_x_assum irule >> simp[] >>
     rpt conj_tac
     >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
     >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
     >- (rpt strip_tac >>
         qpat_x_assum `!H. valid_horizon _ _ _ _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >> simp[expr_post_def])
     >- (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
         gvs[body_exprs_full_ok_def, bind_def, AllCaseEqs()] >> metis_tac[])
     >- (qexistsl_tac [`shadow_func`, `s1'`, `shadow_sm`, `ty`] >> simp[])
     >- (qexists_tac `tops` >> simp[])
     >- (qexistsl_tac [`ann`, `done ++ [e]`, `entry`, `env`] >>
         pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[])) >>
  qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx rest) _ _ _`
    (fn th => assume_tac th) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_exprs cx rest) _ Qtail Rtail` >>
  `gas_outcome_full
     (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0
     (bind (eval_exprs cx rest) (\vs. return (v::vs))) (mid,t,G1,tn1)
     (\H raw ee G tn u. ?res.
        raw = (case res of INL vs => INL (v::vs) | INR ex => INR ex) /\
        Qtail H res ee G tn u)
     (\H raw ee gt r. ?res.
        raw = (case res of INL vs => INL (v::vs) | INR ex => INR ex) /\
        Rtail H res ee gt r)` by
    (ho_match_mp_tac (Q.ISPEC `eval_exprs cx rest`
       (Q.GEN `source` gas_outcome_full_source_map)) >> simp[] >>
     gen_tac >> Cases_on `eval_exprs cx rest es'` >> Cases_on `q` >>
     simp[bind_def, return_def]) >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_exprs cx rest) _) _ _ _`
    (fn th => irule_at Any th) >>
  reverse conj_tac
  >- (simp[Abbr `Rtail`] >> rpt strip_tac >>
      Cases_on `res'` >> gvs[wb_args_exit_def]) >>
  simp[Abbr `Qtail`] >> rpt strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (`valid_horizon cx st0 H (mid with gas_obs := xs).storage_trace` suffices_by simp[] >>
     irule (Q.ISPEC `bind (eval_exprs cx rest) (\vs. vyperState$return (v::vs))`
       (Q.GEN `f` vyperStorageFootprintTheory.valid_horizon_frame)) >>
     qexistsl_tac [`res`, `rest`, `ee with gas_obs := []`, `v`] >>
     simp[] >> conj_tac
     >- (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
              vyperStorageTraceTheory.storage_trace_frame_return]) >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
        (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` (qspec_then `[]` mp_tac) >>
         strip_tac >> drule (SRULE [SF ETA_ss] exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
      `valid_horizon cx st0 H es.storage_trace` by
        (`valid_horizon cx st0 H
            (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []).storage_trace`
           suffices_by simp[] >>
         irule (Q.ISPEC `bind (eval_expr cx e) (read_result cx)`
           (Q.GEN `f` vyperStorageFootprintTheory.valid_horizon_frame)) >>
         qexistsl_tac [`e`, `INL v`, `mid with gas_obs := []`] >>
         simp[]
         >- (irule storage_trace_frame_bind_all >>
             simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
         qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
           (qspec_then `[]` mp_tac) >> simp[]) >>
      `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  conj_tac
  >- (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
      simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      irule typed_args_post_cons >> simp[] >>
      qexistsl_tac [`mid`, `s1`, `t`] >> simp[]) >>
  qpat_assum `expr_post H ctx func cenv cx e es sa s1 s0 mid v x t`
    (assume_tac o MATCH_MP exprSimWordArgsTheory.expr_post_frame) >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
    (fn ssr => let
       val horizon = hd (snd (strip_comb (concl ssr)));
       val th = SPEC_ALL wordArgsPtrTheory.ghost_kept_at_wb_trans;
       val hv = List.find (fn v => fst (dest_var v) = "H") (free_vars (concl th));
     in irule (INST_TYPE (match_type (type_of (valOf hv)) (type_of horizon)) th) end) >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qexistsl_tac [`H`, `ctx`, `cx`, `func`] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G1`, `mid`, `mid`, `t`, `s1`, `tn1`] >> simp[]
QED
