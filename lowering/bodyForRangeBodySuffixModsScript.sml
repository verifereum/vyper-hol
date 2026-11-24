(* Linked Range rounds: source cleanup and the target's matching landing. *)
Theory bodyForRangeBodySuffixMods
Ancestors
  bodyForRangeHeaderMods bodyFullForRange bodyFullForControl
  bodyForRangePopTypingMods bodyForRangePopCellsMods bodyForRangeLandingMods
  gasOutcomeFullPostMods
  gasOutcomeIfSuffixMods gasOutcomeFullMods gasExemptCertMods gasSummaryCompose gasStorage
  fragGasOriginPtr fragExec list finite_map
  bodyFullShadowBodyInv bodyFullPostsMods bodyFullShared bodyPtrDefs bodyMemoryDefs
  bodySimFull stmtFragPtr stmtSimProps stmtSimDefs loweringPosts loweringStateRelDefs
  compileEnv exprLoweringProps allocaHistory venomInst venomExecSemantics venomState
  ptrDiscipline freshWrites bodyFullIfExpReach bodyInvSplit
  stmtSimForArrayLoop stmtSimForLoop vyperEvalPreservesScopes
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
Libs
  monadsyntax

val _ = Parse.hide "body";
val _ = Parse.hide "finish";

Definition range_loop_result_mods_def:
  range_loop_result_mods (raw : unit + exception) =
    case raw of INL u => INL F | INR ex =>
      if ex = BreakException then INL T
      else if ex = ContinueException then INL F else INR ex
End

Theorem range_cleanup_replay[local]:
  eval_stmts cx body ei = (raw,ee) /\ ee.scopes = sc :: rest ==>
  finally (try (ignore_bind (eval_stmts cx body) (return F))
           handle_loop_exception) pop_scope ei =
    (range_loop_result_mods raw, ee with scopes := rest)
Proof
  strip_tac >> Cases_on `raw` >>
  simp[range_loop_result_mods_def, finally_def, try_def, ignore_bind_def,
       bind_def, return_def, pop_scope_def] >>
  rename1 `handle_loop_exception ex` >>
  Cases_on `ex = BreakException` >> Cases_on `ex = ContinueException` >>
  gvs[handle_loop_exception_def, return_def, raise_def, bind_def, pop_scope_def]
QED

Theorem range_cleanup_bad_storage[local]:
  gas_bad_storage_at cx st0 (eval_stmts cx body) ei s marks ==>
  gas_bad_storage_at cx st0
    (finally (try (ignore_bind (eval_stmts cx body) (return F))
                  handle_loop_exception) pop_scope) ei s marks
Proof
  rewrite_tac[gas_bad_storage_at_def] >> strip_tac >> gen_tac >>
  qmatch_goalsub_abbrev_tac `finally _ _ st` >>
  `?xs. (SND (finally (try (ignore_bind (eval_stmts cx body) (return F))
            handle_loop_exception) pop_scope st)).storage_trace =
         (SND (eval_stmts cx body st)).storage_trace ++ xs` by
    (irule finally_try_trace >>
     simp[storage_trace_frame_loop_handler, storage_trace_frame_pop_scope]) >>
  first_x_assum (qspec_then `tail` mp_tac) >> simp[Abbr `st`] >>
  metis_tac[storage_trace_domain_prefix]
QED

Theorem range_cleanup_cert[local]:
  gas_exempt_cert_mods T mods (ctx,func)
    (ignore_bind (eval_stmts cx body) (return ()))
    (ei,s) marks (err,ee) (leaf,finish) /\ ee.scopes = sc :: rest ==>
  gas_exempt_cert_mods T mods (ctx,func)
    (ignore_bind
       (finally (try (ignore_bind (eval_stmts cx body) (return F))
                    handle_loop_exception) pop_scope) (return ()))
    (ei,s) marks (err,ee with scopes := rest) (leaf,finish)
Proof
  strip_tac >>
  rewrite_tac[ignore_bind_finally_unit, ignore_bind_try_unit,
              ignore_bind_return_twice] >>
  irule gas_exempt_cert_mods_cleanup >> qexists_tac `ee` >>
  conj_tac >- simp[pop_scope_def, return_def, evaluation_state_component_equality] >>
  irule gas_exempt_cert_mods_handler >> qexists_tac `ee` >>
  simp[handle_loop_exception_def, ignore_bind_def, bind_def, raise_def,
       evaluation_state_component_equality]
QED

Theorem range_cleanup_nonempty[local]:
  eval_stmts cx body st = (raw,ee) /\ st.scopes <> [] ==>
  ?sc rest. ee.scopes = sc :: rest
Proof
  strip_tac >> drule eval_stmts_preserves_scopes_len >>
  Cases_on `ee.scopes` >> Cases_on `st.scopes` >> simp[] >> fs[]
QED

(* Retain the real source replay alongside the per-horizon body post. *)
Theorem range_cleanup_outcome_mods[local]:
  ei.scopes <> [] /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmts cx body) (ei,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (finally (try (ignore_bind (eval_stmts cx body) (return F))
                 handle_loop_exception) pop_scope) (ei,s,G,tn)
    (\H res ee G1 tn1 t. ?raw sc gs.
      res = range_loop_result_mods raw /\
      eval_stmts cx body (ei with gas_obs := gs) =
        (raw,ee with scopes := sc :: ee.scopes) /\
      Q H raw (ee with scopes := sc :: ee.scopes) G1 tn1 t)
    (\H res ee gt r. ?raw sc. res = range_loop_result_mods raw /\
      R H raw (ee with scopes := sc :: ee.scopes) gt r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_full_mods_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- (rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >> disj1_tac >>
      conj_tac >- (irule range_cleanup_bad_storage >> simp[]) >> metis_tac[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (drule gas_exempt_cert_execution_mods >> strip_tac >>
      qpat_x_assum `!tail. ignore_bind _ _ _ = _`
        (qspec_then `[]` (mp_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
      disch_then (strip_assume_tac o SRULE [ignore_bind_def, bind_def, AllCaseEqs()]) >>
      drule range_cleanup_nonempty >> simp[] >> strip_tac >>
      rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
      disj2_tac >> disj2_tac >>
      qexistsl_tac [`err`, `ee with scopes := rest`, `leaf`, `leaf_pg`,
                   `leaf_g`, `leaf_tn`, `finish`] >>
      conj_tac >- (irule range_cleanup_cert >> goal_assum (drule_at Any) >> simp[]) >>
      metis_tac[]) >>
  qpat_assum `!tail. eval_stmts _ _ _ = _`
    (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
  drule range_cleanup_nonempty >> simp[] >> strip_tac >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks` >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`range_loop_result_mods res`, `ee with scopes := rest`, `r`, `G'`, `tn'`] >>
  conj_tac
  >- (gen_tac >> qpat_assum `!tail. eval_stmts _ _ _ = _`
        (qspec_then `tail` (mp_then Any mp_tac range_cleanup_replay)) >>
      simp[evaluation_state_component_equality]) >>
  simp[] >> gen_tac >> disch_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
  >- (simp[exit_result_def] >> qexistsl_tac [`res`,`sc`,`gas_explicit marks s.vs_gas_readings`] >>
      `ee with <|scopes := sc::rest; gas_obs := []|> = ee with gas_obs := []` by
        simp[evaluation_state_component_equality] >> simp[]) >>
  disj2_tac >> simp[] >> qexistsl_tac [`res`,`sc`] >>
  `ee with <|scopes := sc::rest; gas_obs := []|> = ee with gas_obs := []` by
    simp[evaluation_state_component_equality] >> simp[]
QED

Theorem range_pop_local_lookup[local]:
  cenv_top_ext cenv cb (sc :: rest) /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  lookup_scopes n rest = SOME entry ==>
  lookup_scopes n (sc :: rest) = SOME entry /\
  FLOOKUP cb.ce_vars n = FLOOKUP cenv.ce_vars n
Proof
  strip_tac >>
  `n NOTIN FDOM sc` by (strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac >- simp[FLOOKUP_DEF, lookup_scopes_def] >>
  CCONTR_TAC >> fs[cenv_top_ext_def] >>
  qpat_x_assum `!n. FLOOKUP cb.ce_vars n <> _ ==> _` drule >> simp[]
QED

Theorem range_pop_ghost[local]:
  ghost_inv_at_mods D lo d cb cx (ee with scopes := sc :: ee.scopes) G tn u /\
  cenv_top_ext cenv cb (sc :: ee.scopes) /\
  (!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) ==>
  ghost_inv_at_mods D lo d cenv cx ee G tn u
Proof
  strip_tac >>
  `cb.ce_modules = cenv.ce_modules /\ cb.ce_module_vars = cenv.ce_module_vars /\
   cb.ce_return_buf = cenv.ce_return_buf /\ cb.ce_return_pc = cenv.ce_return_pc /\
   cb.ce_imm_alloca = cenv.ce_imm_alloca` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  fs[ghost_inv_at_mods_def, imm_section_dead_mods_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_all range_pop_local_lookup >> strip_tac >>
      qpat_x_assum `!name entry p sz. lookup_scopes _ (sc :: _) = _ /\ _ ==> _`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >> simp[]) >>
  Cases_on `d` >- fs[return_buf_ptr_def] >>
  rename1 `return_buf_ptr (SOME ds) _ _ _ _` >> PairCases_on `ds` >>
  fs[return_buf_ptr_def]
QED

Theorem range_pop_local_region[local]:
  cenv_top_ext cenv cb (sc :: rest) /\
  (!n. n IN FDOM sc ==> lookup_scopes n rest = NONE) /\
  local_region (cenv with ce_module := src) rest u n b sz ==>
  local_region (cb with ce_module := src) (sc :: rest) u n b sz
Proof
  simp[local_region_def] >> strip_tac >> drule_all range_pop_local_lookup >> strip_tac >>
  qexistsl_tac [`entry`, `p`] >> simp[]
QED

Theorem range_pop_immutable[local]:
  immutable_frame_mods func cb cx (ee with scopes := sc :: ee.scopes) u /\
  cenv_top_ext cenv cb (sc :: ee.scopes) /\
  (!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) ==>
  immutable_frame_mods func cenv cx ee u
Proof
  strip_tac >>
  `cb.ce_modules = cenv.ce_modules /\ cb.ce_module_vars = cenv.ce_module_vars /\
   cb.ce_module_var_type = cenv.ce_module_var_type /\ cb.ce_is_ctor = cenv.ce_is_ctor` by
    fs[cenv_top_ext_def, compile_env_component_equality] >>
  `!src n b sz. local_region (cenv with ce_module := src) ee.scopes u n b sz ==>
     local_region (cb with ce_module := src) (sc :: ee.scopes) u n b sz` by
    (rpt gen_tac >> strip_tac >> irule range_pop_local_region >> simp[] >>
     qexists_tac `cenv` >> simp[]) >>
  fs[immutable_frame_mods_def] >> conj_tac
  >- (qpat_x_assum `immutables_rel_mods _ _ _ _ _` mp_tac >>
      simp[immutables_rel_mods_def, immutables_rel_def]) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  simp[immutable_alloca_sep_def, immutable_decl_sep_alt] >>
  strip_tac >> conj_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (rpt gen_tac >> strip_tac >> first_x_assum irule >> qexists_tac `id` >>
    first_x_assum irule >> simp[]))
QED

Theorem range_scope_cleanup[local]:
  eval_stmts cx body ei = (raw,ee with scopes := sc :: ee.scopes) /\
  ei.scopes <> [] /\ (!n. n IN FDOM (HD ei.scopes) ==> lookup_scopes n (TL ei.scopes) = NONE) /\
  cenv_top_ext cenv bc ei.scopes /\ cenv_top_ext bc cb (sc :: ee.scopes) ==>
  cenv_top_ext cenv cb (sc :: ee.scopes) /\
  (!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE) /\
  MAP FDOM (TL ei.scopes) = MAP FDOM ee.scopes
Proof
  strip_tac >>
  `preserves_scopes_dom ei (ee with scopes := sc::ee.scopes)` by
    (drule eval_stmts_preserves_scopes_dom >> simp[]) >>
  `!n. n IN FDOM sc ==> lookup_scopes n ee.scopes = NONE` by
    (gen_tac >> strip_tac >> irule range_full_body_no_shadow >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[]) >>
  conj_tac
  >- (irule cenv_top_ext_trans >> qexistsl_tac [`bc`, `ei.scopes`] >>
      fs[preserves_scopes_dom_def]) >>
  Cases_on `ei.scopes` >> fs[preserves_scopes_dom_def]
QED

Theorem range_exit_after_pop[local]:
  (!tail. stmt_exit_ptr (RetQ H)
          ((ee with scopes := sc::ee.scopes) with gas_obs := tail) raw gt r) /\
  halt_exit H cx (ee with scopes := sc::ee.scopes) raw r /\
  (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z) /\
  res = range_loop_result_mods raw ==>
  ?ex. res = INR ex /\
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
       halt_exit H cx ee (INR ex :unit + exception) r /\
       (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z)
Proof
  strip_tac >>
  Cases_on `raw` >- (first_x_assum (qspec_then `[]` mp_tac) >>
                     Cases_on `r` >> simp[stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def]) >>
  rename1 `range_loop_result_mods (INR ex)` >>
  `ex <> BreakException /\ ex <> ContinueException` by
    (conj_tac >> disch_then (fn th =>
       qpat_assum `!tail. stmt_exit_ptr _ _ (INR ex) _ _`
         (qspec_then `[]` (mp_tac o REWRITE_RULE [th]))) >>
     Cases_on `r` >> simp[stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def]) >>
  qexists_tac `ex` >> simp[range_loop_result_mods_def] >>
  conj_tac >- (gen_tac >> first_x_assum (qspec_then `tail` mp_tac) >> simp[stmt_exit_ptr_def]) >>
  `halt_exit H cx ((ee with scopes := sc::ee.scopes) with
                 <|scopes := ee.scopes; gas_obs := ee.gas_obs|>) (INR ex :unit + exception) r` by
    (irule halt_exit_scopes_gas_obs >> first_assum ACCEPT_TAC) >>
  `((ee with scopes := sc::ee.scopes) with <|scopes := ee.scopes; gas_obs := ee.gas_obs|>) = ee` by
    simp[evaluation_state_component_equality] >>
  gvs[] >> first_assum ACCEPT_TAC
QED

(* The source pop changes the visible locals, not the target cursor. The
   two allocation frames retain their own entry states and id frontiers. *)
Theorem range_body_pop_frame_mods:
  eval_stmts cx body ei = (raw,ee with scopes := sc :: ee.scopes) /\
  ei.scopes <> [] /\
  (!n. n IN FDOM (HD ei.scopes) ==> lookup_scopes n (TL ei.scopes) = NONE) /\
  cenv_top_ext cenv bc ei.scopes /\ cenv_top_ext bc cb (sc :: ee.scopes) /\
  sa.cs_next_id <= sb0.cs_next_id /\ sa.cs_next_var <= sb0.cs_next_var /\
  ret_pc_ok cenv sa u /\ return_buf_frame d bc sb0 u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x u = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es0 sa s0 bc ei u /\
  (!aid off z i.
     FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
     (!n b z'. local_region cenv es0.scopes s0 n b z' ==>
                off + z <= b \/ b + z' <= off) /\
     off <= i /\ i < off + z /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  stmt_state_rel H ctx func cb cx (ee with scopes := sc :: ee.scopes) t /\
  immutable_frame_mods func cb cx (ee with scopes := sc :: ee.scopes) t /\
  storage_well_formed_on cx (ee with scopes := sc :: ee.scopes) (FST H) /\
  return_buf_sep d cb (ee with scopes := sc :: ee.scopes) t /\
  ghost_inv_at_mods (DF H) lo d cb cx (ee with scopes := sc :: ee.scopes) G1 tn1 t /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  u.vs_alloca_next <= t.vs_alloca_next /\
  (!x v. not_fresh_at sb0 x /\ lookup_var x u = SOME v ==> lookup_var x t = SOME v) /\
  (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sb0 x ==>
       FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
  alloca_frame bc ei sb0 u cb (ee with scopes := sc :: ee.scopes) t /\
  (!aid off z i.
     FLOOKUP u.vs_allocas aid = SOME (off,z) /\ aid < sb0.cs_next_id /\
     (!n b z'. local_region bc ei.scopes u n b z' ==>
                off + z <= b \/ b + z' <= off) /\
     off <= i /\ i < off + z /\ i IN tn1.t_mem ==> i IN tn.t_mem) ==>
  stmt_state_rel H ctx func cenv cx ee t /\
  immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\
  return_buf_sep d cenv ee t /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\
  ret_pc_ok cenv sa t /\ return_buf_frame d cenv sb0 t /\
  range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G1 tn1 t
Proof
  strip_tac >> drule_all_then strip_assume_tac range_scope_cleanup >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb0 x` by
    (gen_tac >> strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x v. not_fresh_at sa x /\ lookup_var x u = SOME v ==> lookup_var x t = SOME v` by
    (rpt strip_tac >> qpat_assum `!x v. not_fresh_at sb0 x /\ _ ==> _`
       irule >> simp[]) >>
  conj_tac
  >- (qpat_assum `stmt_state_rel H ctx func cb cx _ t`
        (mp_then Any mp_tac stmt_state_rel_pop_top_ext) >>
      disch_then (qspecl_then [`cenv`, `sc`, `ee.scopes`] mp_tac) >>
      simp[evaluation_state_component_equality]) >>
  conj_tac >- (drule_all range_pop_immutable >> simp[]) >>
  conj_tac
  >- (irule (iffRL storage_well_formed_on_backends) >>
      qexists_tac `ee with scopes := sc :: ee.scopes` >> simp[]) >>
  conj_tac >- (drule_all return_buf_sep_pop >> simp[]) >>
  conj_tac >- (drule_all range_pop_ghost >> simp[]) >>
  conj_tac
  >- (irule ret_pc_ok_frame >> goal_assum (drule_at (Pat `ret_pc_ok _ _ _`)) >> simp[]) >>
  conj_tac
  >- (irule return_buf_frame_frame >>
      goal_assum (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
      simp[] >> qpat_assum `cenv_top_ext cenv bc ei.scopes`
        (mp_tac o MATCH_MP cenv_top_ext_return_buf) >> simp[]) >>
  suspend "original_frame"
QED

Resume range_body_pop_frame_mods[original_frame]:
  `alloca_frame cenv es0 sa s0 cb (ee with scopes := sc :: ee.scopes) t` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame cenv es0 sa s0 _ _ _`)) >>
     goal_assum (drule_at (Pat `alloca_frame bc ei _ u cb _ t`)) >> simp[]) >>
  `alloca_frame cenv es0 sa s0 cenv ee t` by
    (qpat_assum `alloca_frame cenv es0 sa s0 cb _ t` (mp_then Any mp_tac alloca_frame_pop) >>
     disch_then (qspecl_then [`sc`, `ee.scopes`, `cenv`] mp_tac) >>
     simp[evaluation_state_component_equality]) >>
  simp[range_outer_frame_mods_def] >>
  match_mp_tac (Q.INST [`c1` |-> `bc`, `e1` |-> `ei`, `s1` |-> `u`,
                          `sa1` |-> `sb0`, `tn1` |-> `tn`] alloca_taint_kept_trans) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise range_body_pop_frame_mods

(* The body post and reachability must use the same target execution. *)
Theorem range_suffix_headroom[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (ei,u,G,tn) Q R /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst v. frag_reachable ctx func u fn inst v ==> dalloca_fmp_headroom inst v) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (ei,u,G,tn)
    (\H raw ee G1 tn1 t. Q H raw ee G1 tn1 t /\
      !fn inst v. frag_reachable ctx func t fn inst v ==> dalloca_fmp_headroom inst v) R
Proof
  strip_tac >>
  qhdtm_x_assum `gas_outcome_full_mods`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac [gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- simp[] >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> simp[] >>
          qpat_assum `gas_origin_ptr_path _ _ _ (OK _,_,_)`
            (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
          qpat_assum `!fn inst v. frag_reachable ctx func u fn inst v ==> _`
            (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem range_body_suffix_mods:
  ei = es with <|scopes := (FEMPTY |+ (id,<|assignable := F; type := tyv;
                                  value := IntV (n1 + &k); popped := []|>)) :: es.scopes;
                 gas_obs := []|> /\
  expr_sim_inv_mods mods cenv cx env es /\ body_const_cells_agree_mods mods cx env es /\
  lookup_scopes id es.scopes = NONE /\ id NOTIN FDOM env.var_types /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\ value_has_type tyv (IntV (n1 + &k)) /\
  type_stmts (extend_local env id typ F) ret_ty body = SOME env_b /\
  call_evaluation_safe cx (int_calls_stmts body) /\
  cenv_top_ext cenv bc ei.scopes /\
  sa.cs_next_id <= sb0.cs_next_id /\ sa.cs_next_var <= sb0.cs_next_var /\
  ret_pc_ok cenv sa u /\ return_buf_frame d bc sb0 u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x u = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\ op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es0 sa s0 bc ei u /\
  (!aid off z i.
     FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
     (!n b z'. local_region cenv es0.scopes s0 n b z' ==>
                off + z <= b \/ b + z' <= off) /\
     off <= i /\ i < off + z /\ i IN tn.t_mem ==> i IN tn0.t_mem) /\
  (~block_is_terminated sb1 ==>
    sj.cs_blocks = sb1.cs_blocks /\ sj.cs_current_bb = sb1.cs_current_bb /\
    sj.cs_current_insts = sb1.cs_current_insts ++
      [mk_inst sb1.cs_next_id JMP [Label incr_lbl] []] /\ fn_has_code sb1 sj func) /\
  sb.cs_current_bb = exit_lbl /\ sb.cs_current_insts = [] /\
  sb0.cs_next_var <= sb.cs_next_var /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst v. frag_reachable ctx func u fn inst v ==> dalloca_fmp_headroom inst v) /\
  not_fresh_at sb0 p /\ not_fresh_at sb0 cv /\ not_fresh_at sb0 ev /\
  lookup_var cv u = SOME (i2w (n1 + &k)) /\ lookup_var ev u = SOME (i2w n2) /\
  lookup_var p u = SOME w /\ FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
  ptr_covers G tn p u sz /\
  op_taint tn (Var cv) = {} /\ op_prov G (Var cv) = NONE /\
  op_taint tn (Var ev) = {} /\ op_prov G (Var ev) = NONE /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmts cx body) (ei,u,G,tn)
    (\H raw pre G1 tn1 t. ?cb.
      stmt_lands (InLoop exit_lbl incr_lbl) sb1 raw t /\ ~t.vs_halted /\
      (raw = INL () ==> ~block_is_terminated sb1 /\ cb = bc_out) /\
      cenv_top_ext bc cb pre.scopes /\
      stmt_state_rel H ctx func cb cx pre t /\ immutable_frame_mods func cb cx pre t /\
      storage_well_formed_on cx pre (FST H) /\ return_buf_frame d cb sb1 t /\
      alloca_history func t /\ return_buf_sep d cb pre t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ u.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cb cx pre G1 tn1 t /\
      (!x v. not_fresh_at sb0 x /\ lookup_var x u = SOME v ==> lookup_var x t = SOME v) /\
      (!a b. FLOOKUP u.vs_allocas a = SOME b ==> FLOOKUP t.vs_allocas a = SOME b) /\
      (!x. not_fresh_at sb0 x ==>
           FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x)) /\
      alloca_frame bc ei sb0 u cb pre t /\
      (!aid off z i.
         FLOOKUP u.vs_allocas aid = SOME (off,z) /\ aid < sb0.cs_next_id /\
         (!n b z'. local_region bc ei.scopes u n b z' ==>
                    off + z <= b \/ b + z' <= off) /\
         off <= i /\ i < off + z /\ i IN tn1.t_mem ==> i IN tn.t_mem))
    (\H raw pre gt r.
      (!tail. stmt_exit_ptr (RetQ H) (pre with gas_obs := tail) raw gt r) /\
      halt_exit H cx pre raw r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z)) /\
  (!H ee G1 tn1 land.
    land.vs_current_bb = incr_lbl /\ land.vs_inst_idx = 0 /\ ~land.vs_halted /\
    lookup_var cv land = SOME (i2w (n1 + &k)) /\ lookup_var ev land = SOME (i2w n2) /\
    lookup_var p land = SOME w /\ FLOOKUP land.vs_allocas aid = SOME (w2n w,sz) /\
    ptr_covers G1 tn1 p land sz /\
    op_taint tn1 (Var cv) = {} /\ op_prov G1 (Var cv) = NONE /\
    op_taint tn1 (Var ev) = {} /\ op_prov G1 (Var ev) = NONE /\
    body_const_cells_agree_mods mods cx env ee /\ expr_sim_inv_mods mods cenv cx env ee /\
    lookup_scopes id ee.scopes = NONE /\ storage_trace_domain cx st0 ee.storage_trace /\
    stmt_state_rel H ctx func cenv cx ee land /\ immutable_frame_mods func cenv cx ee land /\
    storage_well_formed_on cx ee (FST H) /\ ret_pc_ok cenv sa land /\
    return_buf_frame d cenv sb0 land /\ return_buf_sep d cenv ee land /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 land /\
    (!fn inst v. frag_reachable ctx func land fn inst v ==> dalloca_fmp_headroom inst v) /\
    range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G1 tn1 land ==>
    let v = i2w (n1 + &k) + 1w;
        t = jump_to cond_lbl (update_var cv v (update_var nv v land));
        G2 = DRESTRICT (DRESTRICT G1 (COMPL {nv})) (COMPL {cv});
        tn2 = tn1 with t_var := tn1.t_var |+ (nv,{}) |+ (cv,{})
    in
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (land,G1,tn1) [] (OK t,G2,tn2) /\
      range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
        sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w H rs ee G2 tn2 t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (finally (try (ignore_bind (eval_stmts cx body) (return F)) handle_loop_exception) pop_scope)
    (ei,u,G,tn)
    (\H res ee G1 tn1 t. ee.gas_obs = [] /\ ~t.vs_halted /\ ?b. res = INL b /\
      (b ==> range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0 H ee G1 tn1 t) /\
      (~b ==> range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
        sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w H rs ee G1 tn1 t))
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==> !z. (r = Halt z \/ ?ir. r = IntRet ir z) ==> allocas_below_fmp z))
Proof
  strip_tac >>
  `ei.scopes <> [] /\ (!n. n IN FDOM (HD ei.scopes) ==> lookup_scopes n (TL ei.scopes) = NONE)` by
    simp[FDOM_FUPDATE] >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ bodyQ bodyR` >>
  qabbrev_tac `replayQ = \H raw pre G1 tn1 t. bodyQ H raw pre G1 tn1 t /\ ~t.vs_halted /\
    (!fn inst v. frag_reachable ctx func t fn inst v ==> dalloca_fmp_headroom inst v) /\
    ?gs. eval_stmts cx body (ei with gas_obs := gs) = (raw,pre)` >>
  `gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmts cx body) (ei,u,G,tn) replayQ bodyR` by suspend "replay" >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ roundQ roundR` >>
  qabbrev_tac `rawQ = \H raw pre G1 tn1 t.
     (if raw = INR BreakException then
       range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0
         H (pre with scopes := TL pre.scopes) G1 tn1 t
      else (raw = INL () \/ raw = INR ContinueException) /\
       range_header_mods mods DF lo d ctx func cenv cx env id tyv st0
         sa sb0 es0 s0 G0 tn0 n1 n2 bound cond_lbl cv ev p aid sz w
         H rs (pre with scopes := TL pre.scopes) G1 tn1 t)` >>
  `gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (eval_stmts cx body) (ei,u,G,tn) rawQ bodyR` by suspend "suffix" >>
  suspend "cleanup"
QED

Resume range_body_suffix_mods[replay]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H raw pre G1 tn1 t. bodyQ H raw pre G1 tn1 t /\
    !fn inst v. frag_reachable ctx func t fn inst v ==> dalloca_fmp_headroom inst v`, `bodyR`] >>
  rpt conj_tac
  >- (simp[Abbr `replayQ`, NoAsms] >> rpt gen_tac >> strip_tac >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qexists_tac `xs` >>
      `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
      qpat_x_assum `ei = _` kall_tac >>
      qpat_assum `!tail. eval_stmts _ _ _ = _`
        (qspec_then `[]` (mp_tac o REWRITE_RULE [APPEND_NIL])) >>
      qpat_assum `ee with gas_obs := [] = ee` (pure_rewrite_tac o single) >> simp[])
  >- simp[] >>
  irule range_suffix_headroom >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume range_body_suffix_mods[suffix]:
  irule gas_outcome_full_mods_zero_suffix_mono >> qexistsl_tac [`replayQ`,`bodyR`] >>
  simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  rpt gen_tac >> strip_tac >>
  rename1 `!H. valid_horizon cx st0 H pre.storage_trace ==> replayQ H raw pre G1 tn1 t` >>
  qabbrev_tac `land = if raw = INL () then jump_to incr_lbl t else t` >>
  qabbrev_tac `v = i2w (n1 + &k) + (1w:bytes32)` >>
  qabbrev_tac `back = jump_to cond_lbl (update_var cv v (update_var nv v land))` >>
  qabbrev_tac `G2 = DRESTRICT (DRESTRICT G1 (COMPL {nv})) (COMPL {cv})` >>
  qabbrev_tac `tn2 = tn1 with t_var := tn1.t_var |+ (nv,{}) |+ (cv,{})` >>
  qexistsl_tac [`if raw = INR BreakException then land else back`,
                `if raw = INR BreakException then G1 else G2`,
                `if raw = INR BreakException then tn1 else tn2`] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> replayQ _ _ _ _ _ _` (drule_then mp_tac) >>
  simp[Abbr `replayQ`, Abbr `bodyQ`, NoAsms] >> strip_tac >>
  `?sc rest. pre.scopes = sc::rest` by
    (irule range_cleanup_nonempty >> goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >> simp[]) >>
  qabbrev_tac `ee = pre with scopes := rest` >>
  suspend "pop_frame"
QED

Resume range_body_suffix_mods[pop_frame]:
  `pre = ee with scopes := sc::ee.scopes` by
    simp[Abbr `ee`, evaluation_state_component_equality] >>
  `stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
   storage_well_formed_on cx ee (FST H) /\ return_buf_sep d cenv ee t /\
   ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t /\ ret_pc_ok cenv sa t /\
   return_buf_frame d cenv sb0 t /\ range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G1 tn1 t` by
    (irule range_body_pop_frame_mods >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexistsl_tac [`G`,`bc`,`body`,`cb`,`ei with gas_obs := gs`,`raw`,`sc`,`tn`,`u`] >>
     qpat_assum `pre = ee with scopes := _` (pure_rewrite_tac o single o SYM) >>
     simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qpat_assum `cenv_top_ext bc cb pre.scopes` mp_tac >>
     qpat_assum `pre.scopes = sc::rest` (pure_rewrite_tac o single) >> simp[Abbr `ee`, NoAsms]) >>
  suspend "land"
QED

Resume range_body_suffix_mods[land]:
  `raw = INL () ==> ~block_is_terminated sb1` by (strip_tac >> fs[]) >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK land,G1,tn1) /\
   (if raw = INR BreakException then
      range_done_mods DF lo d ctx func cenv cx lctx sa sb es0 s0 G0 tn0 H ee G1 tn1 land
    else (raw = INL () \/ raw = INR ContinueException) /\
      land.vs_current_bb = incr_lbl /\ land.vs_inst_idx = 0 /\ ~land.vs_halted /\
      lookup_var cv land = SOME (i2w (n1 + &k)) /\ lookup_var ev land = SOME (i2w n2) /\
      lookup_var p land = SOME w /\ FLOOKUP land.vs_allocas aid = SOME (w2n w,sz) /\
      ptr_covers G1 tn1 p land sz /\
      op_taint tn1 (Var cv) = {} /\ op_prov G1 (Var cv) = NONE /\
      op_taint tn1 (Var ev) = {} /\ op_prov G1 (Var ev) = NONE /\
      stmt_state_rel H ctx func cenv cx ee land /\ immutable_frame_mods func cenv cx ee land /\
      storage_well_formed_on cx ee (FST H) /\ ret_pc_ok cenv sa land /\
      return_buf_frame d cenv sb0 land /\ return_buf_sep d cenv ee land /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 land /\
      (!fn inst v. frag_reachable ctx func land fn inst v ==> dalloca_fmp_headroom inst v) /\
      range_outer_frame_mods ctx func cenv sa es0 s0 G0 tn0 ee G1 tn1 land)` by
    suspend "landing_rule" >>
  Cases_on `raw = INR BreakException`
  >- gvs[Abbr `land`, Abbr `rawQ`, Abbr `ee`] >>
  qpat_assum `raw <> INR BreakException` (fn not_break =>
    qpat_x_assum `(if raw = INR BreakException then _ else _)`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac o REWRITE_RULE [not_break])) >>
  suspend "backedge"
QED

Resume range_body_suffix_mods[landing_rule]:
  qpat_assum `Abbrev (land = _)` (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) (PURE_REWRITE_RULE [LET_THM] range_body_landing_mods)) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexistsl_tac [`exit_lbl`,`sb1`,`sj`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`G`,`tn`,`u`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume range_body_suffix_mods[backedge]:
  qpat_assum `eval_stmts cx body (ei with gas_obs := gs) = _` mp_tac >>
  qpat_assum `ei = _` (pure_rewrite_tac o single) >>
  simp[NoAsms, evaluation_state_fupdcanon] >> strip_tac >>
  `body_const_cells_agree_mods mods cx env (pre with scopes := rest)` by
    (irule range_body_pop_cells_mods >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qexists_tac `sc` >> first_assum ACCEPT_TAC) >>
     simp[NoAsms, evaluation_state_fupdcanon] >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmts _ _ _ = _`)) >> first_assum ACCEPT_TAC) >>
  `expr_sim_inv_mods mods cenv cx env (pre with scopes := rest) /\ lookup_scopes id rest = NONE` by
    (irule range_body_pop_typing_mods >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qexists_tac `sc` >> first_assum ACCEPT_TAC) >>
     simp[NoAsms, evaluation_state_fupdcanon] >>
     goal_assum (drule_at (Pat `eval_stmts _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `type_stmts _ _ _ = _`)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `storage_trace_domain cx st0 ee.storage_trace` by simp[Abbr `ee`] >>
  qpat_assum `!H ee G1 tn1 land. _ ==> let _ = _ in _`
    (qspecl_then [`H`,`ee`,`G1`,`tn1`,`land`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[Abbr `ee`])) >>
  simp[LET_THM, Excl "DRESTRICT_DRESTRICT", NoAsms] >> strip_tac >>
  simp[Abbr `rawQ`] >>
  conj_tac
  >- (qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK land,G1,tn1)`
        (mp_then (Pos hd) mp_tac gas_origin_ptr_path_append) >>
      simp[Abbr `back`, Abbr `G2`, Abbr `tn2`]) >>
  fs[Abbr `back`, Abbr `G2`, Abbr `tn2`, Abbr `ee`]
QED

Resume range_body_suffix_mods[cleanup]:
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G1 tn1 t. ?raw sc gs.
      res = range_loop_result_mods raw /\
      eval_stmts cx body (ei with gas_obs := gs) = (raw,ee with scopes := sc::ee.scopes) /\
      rawQ H raw (ee with scopes := sc::ee.scopes) G1 tn1 t`,
    `\H res ee gt r. ?raw sc. res = range_loop_result_mods raw /\
                         bodyR H raw (ee with scopes := sc::ee.scopes) gt r`] >>
  rpt conj_tac
  >- (simp[Abbr `rawQ`, Abbr `roundQ`, NoAsms] >> rpt gen_tac >> strip_tac >>
      Cases_on `raw = INR BreakException` >> gvs[range_loop_result_mods_def] >>
      qpat_x_assum `raw = INL () \/ _` strip_assume_tac >> gvs[range_loop_result_mods_def])
  >- (simp[Abbr `bodyR`, Abbr `roundR`, NoAsms, evaluation_state_fupdcanon] >>
      rpt gen_tac >> strip_tac >>
      irule range_exit_after_pop >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`raw`,`sc`] >>
      simp[NoAsms, evaluation_state_fupdcanon] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule range_cleanup_outcome_mods >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise range_body_suffix_mods
