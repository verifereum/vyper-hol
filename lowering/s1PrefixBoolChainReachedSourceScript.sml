(* Replay a reached native call at the marks of the enclosing operand. *)
Theory s1PrefixBoolChainReachedSource
Ancestors
  s1PrefixCompose s1PrefixDefs s1PrefixProps gasOutcomeFull contextCodegenRelProps
  bodyFullRawCallCallOrigin
  bodyPtrMakeArrayEmission exprSimAccounts bodyFullHashKeccakFixed
  vyperCallOutcomeProps vyperState bodyPtrDefs ptrDiscipline
  fragGasOriginPtr fragExec venomExecSemantics venomInst gasShadowState
  gasShadow gasExplicitSites exprLowering list arithmetic

(* Locate the one ordinary outcome after the input trace.  Computed
   precompiles may occur on either side of the native event. *)
Triviality native_source_trace_position:
  (initial ++ prior) ++ StorageOutcome rq oc :: later =
    seen ++ StorageOutcome rq' oc' :: rest /\
  LENGTH initial <= LENGTH seen /\ ~computed_precompile rq' /\
  EVERY (\ob. !r o'. ob = StorageOutcome r o' ==> computed_precompile r) prior /\
  EVERY (\ob. !r o'. ob = StorageOutcome r o' ==> computed_precompile r) later ==>
  seen = initial ++ prior /\ rq' = rq /\ oc' = oc
Proof
  qid_spec_tac `seen` >> Induct_on `initial`
  >- (simp_tac bool_ss [APPEND,LENGTH,ZERO_LESS_EQ] >> Induct_on `prior`
      >- (Cases_on `seen`
          >- simp_tac bool_ss [APPEND,CONS_11,storage_trace_event_11] >>
          simp_tac bool_ss [APPEND,CONS_11,EVERY_APPEND,EVERY_DEF] >>
          strip_tac >>
          qpat_x_assum `EVERY _ later` mp_tac >>
          ASM_REWRITE_TAC[EVERY_APPEND,EVERY_DEF] >> metis_tac[]) >>
      Cases_on `seen`
      >- (simp_tac bool_ss [APPEND,CONS_11,EVERY_DEF] >> rpt strip_tac >>
          first_x_assum (qspecl_then [`rq'`,`oc'`] mp_tac) >> ASM_REWRITE_TAC[]) >>
      simp_tac bool_ss [APPEND,CONS_11,EVERY_DEF] >> metis_tac[]) >>
  Cases_on `seen` >> simp_tac bool_ss [APPEND,CONS_11,LENGTH,LESS_EQ_MONO,NOT_SUC_LESS_EQ_0] >>
  metis_tac[]
QED

(* The ledger's emitted instruction is fetched at the actual call cut;
   pointer and memory safety come from the native step, not from its PC. *)
Theorem reached_staticcall_request_site:
  emit_op STATICCALL [gas;addr;dp;dl;buf;rz] sc = (Var out,sd) /\
  fn_has_code sc sd func /\
  ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
  t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  step_inst_base (mk_inst sc.cs_next_id STATICCALL [gas;addr;dp;dl;buf;rz] [out]) t = OK post /\
  inst_mem_below_frontier (mk_inst sc.cs_next_id STATICCALL [gas;addr;dp;dl;buf;rz] [out]) t /\
  eval_operand dp t = SOME ao /\ eval_operand dl t = SOME az /\
  eval_operand buf t = SOME ro /\ eval_operand rz t = SOME rn /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p t (w2n az)) /\
  (rn <> 0w ==> ?p. buf = Var p /\ ptr_covers G tn p t (w2n rn)) /\
  EVERY (\p. op_taint tn p = {}) [gas;addr;dp;dl;buf;rz] /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  ghost_inv_at D lo d cenv cx cut G tn t /\
  stmt_state_rel H ctx func cenv cx cut t /\
  stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed)) post /\
  take_request_outcome rq0 cut = (INL (rq,oc),consumed) /\
  LENGTH cut.requests = k /\ ~computed_precompile rq ==>
  request_site (D,lo,explicit,ctx,func,PG) cx H (t,G,tn) k rq oc
Proof
  strip_tac >> drule_all ordinary_request_index >> strip_tac >>
  drule_all emit_op_fetch_boundary >>
  disch_then (qx_choose_then `tmp` (qx_choose_then `bb` strip_assume_tac)) >>
  `tmp = out` by fs[] >>
  pop_assum SUBST_ALL_TAC >>
  qabbrev_tac `inst = mk_inst sc.cs_next_id STATICCALL [gas;addr;dp;dl;buf;rz] [out]` >>
  `inst.inst_opcode = STATICCALL /\ inst.inst_operands = [gas;addr;dp;dl;buf;rz]` by
    simp[Abbr `inst`,mk_inst_def] >>
  `stor_taint_ok_at D tn t /\ allocas_from lo t` by
    (qhdtm_assum `ghost_inv_at` (mp_tac o REWRITE_RULE [ghost_inv_at_def]) >> simp[]) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ cut t`
    (mp_then Any assume_tac stmt_state_rel_allocas_below_fmp) >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb t.vs_inst_idx = SOME inst` by simp[Abbr `inst`] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) []
     (OK (post with vs_inst_idx := SUC t.vs_inst_idx),
      step_prov PG G inst post,step_taint inst t post tn)` by
    (irule raw_call_step_origin_full >> simp[] >>
     qpat_assum `t.vs_inst_idx = _` (fn eq => rewrite_tac[GSYM eq]) >>
     first_assum ACCEPT_TAC) >>
  `MEM inst.inst_opcode [CALL;STATICCALL;DELEGATECALL] /\ inst.inst_opcode <> INVOKE` by simp[] >>
  drule_all call_step_checks >> strip_tac >>
  `active_inst func inst t` by (irule lookup_instruction_active >> metis_tac[]) >>
  rewrite_tac[request_site_def] >>
  qexistsl_tac [`[]`,`func`,`PG`,`G`,`tn`,`t`,`inst`,`0`,`post`] >>
  simp[gas_origin_ptr_focus_nil,step_inst_non_invoke]
QED

(* The source ledger splits execution into a prelude, the selected oracle
   action, and its continuation.  The focus used to witness the marks
   needs only an input-compatible horizon; the site uses the horizon of
   the trace before the call, not that of the completed expression. *)
Theorem bool_chain_reached_native_source_prefix:
  lower_value compile_expr cenv ty h sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr h) shadow_sa =
    (op,shadow_sb) /\
  gas_shadow_state sc shadow_sc /\ gas_shadow_state sd shadow_sd /\
  emit_op STATICCALL [gas;addr;dp;dl;buf;rz] sc = (Var out,sd) /\
  emit_op STATICCALL [gas;addr;dp;dl;buf;rz] shadow_sc = (Var out,shadow_sd) /\
  cs_extends sa sc /\ cs_extends sd sb /\ fn_has_code sa sb func /\
  cs_extends shadow_sa shadow_sc /\ cs_extends shadow_sd shadow_sb /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
  t.vs_inst_idx = LENGTH sc.cs_current_insts /\
  step_inst_base (mk_inst sc.cs_next_id STATICCALL [gas;addr;dp;dl;buf;rz] [out]) t = OK post /\
  inst_mem_below_frontier (mk_inst sc.cs_next_id STATICCALL [gas;addr;dp;dl;buf;rz] [out]) t /\
  eval_operand dp t = SOME ao /\ eval_operand dl t = SOME az /\
  eval_operand buf t = SOME ro /\ eval_operand rz t = SOME rn /\
  (az <> 0w ==> ?p. dp = Var p /\ ptr_covers G tn p t (w2n az)) /\
  (rn <> 0w ==> ?p. buf = Var p /\ ptr_covers G tn p t (w2n rn)) /\
  op_prov G addr = NONE /\
  EVERY (\p. op_taint tn p = {}) [gas;addr;dp;dl;buf;rz] /\
  (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tn.t_mem) /\
  requests_outcomes_frame prelude /\
  (!tail. prelude (ee with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
    (INL (),cut with gas_obs := tail)) /\
  take_request_outcome rq0 cut = (INL (rq,oc),consumed) /\
  (!tail. cont (rq,oc) (consumed with gas_obs := tail) = (res,mid with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx h) (read_result cx)
      (ee with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
    bind prelude (\(). bind (take_request_outcome rq0) cont)
      (ee with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail)) /\
  cut.storage_trace = ee.storage_trace ++ prior /\
  mid.storage_trace = consumed.storage_trace ++ later /\
  EVERY (\ob. !r o'. ob = StorageOutcome r o' ==> computed_precompile r) prior /\
  EVERY (\ob. !r o'. ob = StorageOutcome r o' ==> computed_precompile r) later /\
  (?H leaf leaf_pg leaf_g leaf_tn stop.
     (storage_trace_domain cx st0 ee.storage_trace ==> valid_horizon cx st0 H ee.storage_trace) /\
     gas_origin_ptr_focus (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (u,J,tm) marks (leaf,leaf_pg,leaf_g,leaf_tn,stop)) /\
  (!H. valid_horizon cx st0 H cut.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (u,J,tm) marks (OK t,G,tn) /\
     stmt_state_rel H ctx func cenv cx cut t /\
     stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq oc consumed)) post /\
     ghost_inv_at (DF H) lo d cenv cx cut G tn t) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (bind (eval_expr cx h) (read_result cx)) (ee,u,J,tm)
Proof
  strip_tac >>
  `fn_has_code sc sd func` by
    (irule fn_has_code_mid >> conj_tac
     >- metis_tac[emit_op_extends_next_var] >>
     qexistsl_tac [`sb`,`sa`] >> simp[]) >>
  `!tail. bind (eval_expr cx h) (read_result cx)
          (ee with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail) =
        (res,mid with gas_obs := tail)` by
    (gen_tac >>
     qpat_assum `!tail. bind (eval_expr cx h) _ _ = _`
       (qspec_then `tail` (fn eq => REWRITE_TAC[eq])) >>
     simp[bind_def,take_request_gas_obs]) >>
  `mid.storage_trace = (ee.storage_trace ++ prior) ++ StorageOutcome rq oc :: later` by
    (drule take_request_outcome_success >> strip_tac >> fs[APPEND_ASSOC]) >>
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `marks` >>
  conj_tac >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`stop`] >> simp[]) >>
  map_every qx_gen_tac [`tail`,`ans`,`endst`,`seen`,`rq'`,`oc'`,`rest`,`Hsite`] >>
  strip_tac >>
  `(ee.storage_trace ++ prior) ++ StorageOutcome rq oc :: later =
      seen ++ StorageOutcome rq' oc' :: rest` by
    (qpat_assum `!tail. bind (eval_expr cx h) _ _ = (res,_)`
       (qspec_then `tail` mp_tac) >> simp[] >>
     strip_tac >> fs[APPEND_ASSOC]) >>
  drule_all native_source_trace_position >>
  disch_then (map_every SUBST_ALL_TAC o CONJUNCTS) >>
  `valid_horizon cx st0 Hsite cut.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon cx st0 H cut.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `LENGTH cut.requests = recorded_outcomes_count cut.storage_trace` by
    (qhdtm_assum `requests_outcomes_frame`
       (qspec_then `ee with gas_obs := gas_explicit marks u.vs_gas_readings ++ tail` mp_tac o
        REWRITE_RULE [requests_outcomes_frame_def,vyperCallOutcomeFrameTheory.state_rel_frame_def]) >>
     simp[]) >>
  irule request_site_prepend_path >> qexistsl_tac [`G`,`marks`,`t`,`tn`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `recorded_outcomes_count (ee.storage_trace ++ prior) = LENGTH cut.requests` by fs[] >>
  pop_assum SUBST1_TAC >>
  `LENGTH cut.requests = LENGTH cut.requests` by simp[] >>
  drule_all_then MATCH_ACCEPT_TAC reached_staticcall_request_site
QED
