(* Linked Range rounds: source cleanup and the target's matching landing. *)
Theory bodyForRangeBodySuffixMods
Ancestors
  bodyForRangeHeaderMods bodyFullForRange bodyFullForControl
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
