(* Residual assignment prefixes end at the target evaluation cut. *)
Theory s1PrefixAssignResidualTarget
Ancestors
  s1PrefixTarget s1PrefixImmutableTargetPlace s1PrefixOfVV s1PrefixDefs
  bodyPtrPopTargetFragTransport tuplePlaceStep targetPlaceSim
  bodyFullPreds bodyFullTargetDefs bodySimFull bodySim
  vyperInterpreter vyperState gasSummary compileEnv

Theorem residual_write_keeps_target_prefix[local]:
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 source (mid,u,Gu,tnu) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind source (\p. write_place cx p v)) (mid,u,Gu,tnu)
Proof
  rewrite_tac[gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `source (mid with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail)` >>
  rename1 `source _ = (ans,ep)` >>
  `ee.storage_trace = ep.storage_trace` by
    (qpat_x_assum `bind _ _ _ = (_,ee)` mp_tac >>
     Cases_on `ans` >> simp[Once bind_def] >>
     disch_then (mp_tac o MATCH_MP write_place_storage_trace) >> simp[]) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (qspec_then `tail` irule) >>
  simp[] >> qexistsl_tac [`ep`,`ans`,`sfx`,`tail`] >> fs[]
QED

Theorem body_assign_residual_target_write_prefix:
  !t DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env mid
   st0 vt sa sb shadow_sa shadow_sb r u Gu tnu v.
    (~immutable_root cx t \/ (?root. t = TopLevelNameTarget root)) /\
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_base_target_full_ok cx t /\ body_base_target_prefix_ok cx t /\
    body_const_cells_agree [(NONE,tops)] cx env mid /\
    expr_sim_inv cenv cx env mid /\ target_indices_pre cenv cx env t /\
    type_place_target env t = SOME vt /\
    compile_get_target_ptr compile_expr cenv t sa = (r,sb) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
      (gas_shadow_target t) shadow_sa = (r,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (eval_target_place cx t) target_place_res_ok mid /\
    return_buf_frame d cenv sa u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn inst s. frag_reachable ctx func u fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid u /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid Gu tnu u) /\ ~u.vs_halted /\
    u.vs_current_bb = sa.cs_current_bb /\ u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (bind (eval_target_place cx t) (\p. write_place cx p v)) (mid,u,Gu,tnu)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule residual_write_keeps_target_prefix >>
  Cases_on `?root. t = TopLevelNameTarget root`
  >- (qpat_x_assum `?root. _` (qx_choose_then `root` SUBST_ALL_TAC) >>
      PairCases_on `root` >> simp[immutable_toplevel_target_prefix]) >>
  `target_pre cenv cx env t mid` by fs[target_pre_def] >>
  `gas_admissible (eval_base_place cx t) target_res_ok mid` by
    metis_tac[eval_target_place_as_bind, get_place_base_admissible] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_base_place cx t) (mid,u,Gu,tnu)` by
    (drule_all body_target_sim_prefix >> disch_then (qspec_then `PG` ACCEPT_TAC)) >>
  `!ee. SND (eval_target_place cx t ee) = SND (eval_base_place cx t ee)` by
    simp[eval_target_place_as_bind, get_place_bind_state] >>
  drule gas_prefix_full_state_cong >> simp[]
QED
