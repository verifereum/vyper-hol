Theory concretizeLayoutDelegate
Ancestors concretizeLayoutCutSafe concretizeLayoutDelegateBoundary
  concretizeLayoutExternalCall concretizeLayoutExternalRequests
  venomCallOracleDefs extCallOracle lowerDloadExternalEffects
  concretizeLayoutCleanRead concretizeLayoutSupplement concretizeLayoutReaderContext
  frameRelocationEnvironment frameRelocationAllocationSteps frameRelocationMemory
  venomExecSemantics venomState ptrDiscipline list venomMemProps
  frameRelocationLocal frameRelocationValues frameRelocationGuardedValues
  frameRelocationStoreSteps frameRelocationGhostCopy frameRelocationDemand
  frameOriginUpdates finite_map frameRelocationTaintOrder frameRelocationCopyTaint
  codegenRel memLocDefs contextCodegenRel
  o1PassContract frameRelocationCleanOperands pointerConfinedDefs
  concretizeLayoutLocalCalldataCopy frameRelocationReachableSupport
  frameResolvedTrace frameOriginReachable frameOriginHistory
  frameJointTransition frameJointDemand frameJointTrace
  frameActivationLookup frameActivationLifetime concretizeLayoutLocalSha3
  concretizeLayoutLocalReturnCopy words

Theorem delegate_success_envelope:
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post ==>
  ?out w p. inst.inst_outputs = [out] /\
    consume_call_outcome (venom_call_request s addr 0w off sz F with
      <|cr_kind := DelegateMessageCall; cr_gas := SOME (w2n gas)|>)
      (w2n ro) (w2n rs) s = (w,p) /\
    post = update_var out w p
Proof
  simp[exec_delegatecall_def, AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  strip_tac >> pairarg_tac >> gvs[AllCaseEqs(), Excl "consume_call_outcome_eq"] >>
  metis_tac[]
QED

Theorem delegate_taint:
  inst.inst_opcode = DELEGATECALL /\ inst.inst_outputs = [v] /\
  inst.inst_operands = [opg;opa;opd;opn;opr;opm] /\
  post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp ==>
  step_taint inst s post tn =
    tn with <|t_mem := tn.t_mem DIFF range_bytes (step_writes inst s post);
              t_var := tn.t_var |+ (v,{});
      t_stor := if (adopt_guard s.vs_call_ctx.cc_static s post (HD s.vs_outcomes).co_success) then {} else tn.t_stor;
      t_trans := if (adopt_guard s.vs_call_ctx.cc_static s post (HD s.vs_outcomes).co_success) then {} else tn.t_trans|>
Proof
  strip_tac >>
  `new_site_bytes s post = {}` by
    (irule new_site_bytes_unchanged >> simp[]) >>
  simp[step_taint_def, mem_taint_def, written_taint_def, out_taint_def,
       set_var_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
       taint_component_equality]
QED

Theorem concretize_delegate_observation:
  inst.inst_opcode = DELEGATECALL /\ taint_ok fn tn inst s /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  relocation_env s t /\ relocation_reader_context s t /\
  concretize_local_obs s t /\ concretize_supplement D tn s t /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n (offT:bytes32)) (w2n sz) t /\
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post ==>
  ?post'. exec_delegatecall inst t gas addr offT sz (roT:bytes32) rs = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    relocation_env post post' /\ relocation_reader_context post post' /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)
Proof
  strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by fs[relocation_env_def] >>
  `s.vs_outcomes = t.vs_outcomes` by fs[concretize_supplement_def] >>
  `s.vs_outcomes <> []` by
    (CCONTR_TAC >> gvs[exec_delegatecall_def, AllCaseEqs()]) >>
  `t.vs_outcomes <> []` by metis_tac[] >>
  drule delegate_success_envelope >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_call_outcome rq _ _ s = _` >>
  qabbrev_tac `rqT = venom_call_request t addr 0w offT sz F with
    <|cr_kind := DelegateMessageCall; cr_gas := SOME (w2n gas)|>` >>
  `rq.cr_accounts = s.vs_accounts /\ rqT.cr_accounts = t.vs_accounts /\
   rq.cr_tStorage = s.vs_transient /\ rqT.cr_tStorage = t.vs_transient /\
   rq.cr_kind = DelegateMessageCall /\
   rq with <|cr_accounts := rqT.cr_accounts; cr_tStorage := rqT.cr_tStorage|> = rqT` by
    simp[Abbr `rq`, Abbr `rqT`, venom_call_request_def] >>
  `request_agree_except D rq rqT` by
    (drule_all concretize_request_observation >> simp[]) >>
  Cases_on `consume_call_outcome rqT (w2n roT) (w2n rs) t` >>
  rename1 `consume_call_outcome rqT _ _ t = (wT,pT)` >>
  drule_all concretize_call_completion_observation >> strip_tac >>
  qexists_tac `update_var out wT pT` >> conj_tac
  >- (gvs[Abbr `rqT`, Excl "consume_call_outcome_eq"] >>
      simp[exec_delegatecall_def, Excl "consume_call_outcome_eq"]) >>
  conj_tac
  >- gvs[concretize_local_obs_def, dead_result_rel_def, update_var_def,
         Excl "consume_call_outcome_eq"] >>
  conj_tac >- suspend "supplement" >>
  conj_tac >- suspend "environment" >>
  conj_tac >- suspend "reader" >>
  qexistsl_tac [`out`,`w`] >> simp[update_var_def]
QED
Resume concretize_delegate_observation[supplement]:
  `LIST_REL (request_agree_except D)
    (record_request rq s.vs_requests) (record_request rqT t.vs_requests)` by
    (irule request_agree_record_request >> fs[concretize_supplement_def]) >>
  fs[concretize_supplement_def] >>
  Cases_on `t.vs_outcomes` >>
  gvs[consume_call_outcome_def, take_outcome_def, computed_precompile_def,
      Abbr `rq`, Abbr `rqT`, venom_call_request_def,
      failed_outcome_def, adopt_outcome_def, Excl "consume_call_outcome_eq"] >>
  Cases_on `h.co_success` >> Cases_on `t.vs_call_ctx.cc_static` >>
  gvs[concretize_supplement_def, step_taint_def, store_taint_def,
      imm_taint_def, adopt_reset_def, update_var_def,
      accounts_agree_except_def, transient_agree_except_def,
      storage_agree_except_def, word_agree_except_def,
      record_request_changed, record_request_def, computed_precompile_def,
      Excl "consume_call_outcome_eq"]
QED
Resume concretize_delegate_observation[environment]:
  gvs[consume_call_outcome_def, update_var_def, relocation_env_def,
      Excl "consume_call_outcome_eq", pairTheory.UNCURRY] >> pairarg_tac >> gvs[]
QED
Resume concretize_delegate_observation[reader]:
  gvs[consume_call_outcome_def, update_var_def, relocation_reader_context_def,
      Excl "consume_call_outcome_eq", pairTheory.UNCURRY] >> pairarg_tac >> gvs[]
QED
Finalise concretize_delegate_observation

Theorem delegate_execution_fields:
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post ==>
  ?out w. inst.inst_outputs = [out] /\
    post.vs_vars = (update_var out w s).vs_vars /\
    post.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rs) post.vs_returndata) s).vs_memory /\
    post.vs_allocas = s.vs_allocas /\ post.vs_fmp = s.vs_fmp
Proof
  strip_tac >> drule delegate_success_envelope >> strip_tac >>
  qmatch_asmsub_abbrev_tac `consume_call_outcome rq _ _ s = _` >>
  Cases_on `take_outcome rq s.vs_outcomes` >>
  rename1 `take_outcome rq s.vs_outcomes = (oc,rest)` >>
  Cases_on `adopt_outcome rq oc (s.vs_accounts,s.vs_transient,s.vs_logs)` >>
  PairCases_on `r` >> drule_all call_completion_fields >> strip_tac >>
  qexistsl_tac [`out`,`w`] >>
  gvs[update_var_def, Excl "consume_call_outcome_eq"]
QED

Theorem concretize_delegate_local_execution:
  inst.inst_opcode = DELEGATECALL /\ taint_ok fn tn inst s /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  inst.inst_operands = [opg;opa;opd;opn;opr;opm] /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  read_memory (w2n off) (w2n sz) s =
    read_memory (w2n (offT:bytes32)) (w2n sz) t /\
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post /\
  (!a b. next a b /\ w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
     b = w2n (roT:bytes32) + (a-w2n ro)) /\
  (!a b. next a b /\ ~(w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata)) ==>
     R a b /\ ~(w2n roT <= b /\
       b < w2n roT + LENGTH (TAKE (w2n rs) post.vs_returndata))) ==>
  ?post'. exec_delegatecall inst t gas addr offT sz roT rs = OK post' /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes Opaque (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn)) next concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    relocation_env post post' /\ relocation_reader_context post post'
Proof
  strip_tac >>
  `concretize_local_obs s t` by metis_tac[local_rel_observation] >>
  `?post'. exec_delegatecall inst t gas addr offT sz roT rs = OK post' /\
    concretize_local_obs post post' /\
    concretize_supplement D (step_taint inst s post tn) post post' /\
    relocation_env post post' /\ relocation_reader_context post post' /\
    (?out w. inst.inst_outputs = [out] /\
      post.vs_vars = (update_var out w s).vs_vars /\
      post'.vs_vars = (update_var out w t).vs_vars)` by
    (irule concretize_delegate_observation >> simp[] >>
     conj_tac >- (qexistsl_tac [`off`,`ro`] >> simp[]) >>
     qexists_tac `fn` >> simp[]) >>
  qexists_tac `post'` >> asm_rewrite_tac[] >>
  `post.vs_returndata = post'.vs_returndata` by
    (fs[concretize_local_obs_def, dead_result_rel_def] >>
     irule listTheory.LIST_EQ >> simp[]) >>
  `demand_agree next (\a. read_byte a post.vs_memory)
    (\b. read_byte b post'.vs_memory)` by suspend "memory" >>
  `local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R (\s t. T) s t` by fs[local_rel_def] >>
  `local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [out] NONE))
    (guarded_bytes Opaque (origin_set rv [out] NONE) (step_taint inst s post tn))
    R (\s t. T) (update_var out w s) (update_var out w t)` by suspend "values" >>
  fs[local_rel_def, variable_domains_def, variables_agree_on_def,
     local_values_def, lookup_var_def, update_var_def]
QED
Resume concretize_delegate_local_execution[memory]:
  drule delegate_execution_fields >> strip_tac >>
  rev_drule delegate_execution_fields >> strip_tac >>
  qpat_x_assum `post.vs_returndata = post'.vs_returndata` SUBST_ALL_TAC >>
  asm_rewrite_tac[] >> irule demand_agree_write_memory >>
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!a b. _ ==> b = _`
      (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> strip_tac >> gvs[]) >>
  qexists_tac `R` >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!a b. _ ==> R a b /\ _`
        (qspecl_then [`a`,`b`] mp_tac) >> simp[] >> metis_tac[]) >>
  metis_tac[local_rel_demand]
QED
Resume concretize_delegate_local_execution[values]:
  irule local_rel_update >> simp[] >>
  (conj_tac >- simp[guarded_bytes_def, frameRelocationGhostCopyTheory.copy_bytes_def,
    word_agree_except_def]) >>
  (conj_tac >- simp[guarded_ptr_def, copy_ptr_def, origin_set_lookup]) >>
  goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
  simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_def,
    frameRelocationGhostCopyTheory.copy_bytes_def, origin_set_lookup,
    step_taint_def, set_var_taint_def, out_taint_def, MEM, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[op_taint_def, FLOOKUP_UPDATE]
QED
Finalise concretize_delegate_local_execution

Theorem concretize_delegate_taint_order:
  inst.inst_opcode = DELEGATECALL /\
  inst.inst_operands = [opg;opa;opd;opn;opr;opm] /\
  eval_operand opg s = SOME gas /\ eval_operand opa s = SOME addr /\
  eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
  eval_operand opg t = SOME gas /\ eval_operand opa t = SOME addr /\
  eval_operand opd t = SOME offT /\ eval_operand opn t = SOME sz /\
  eval_operand opr s = SOME ro /\ eval_operand opm s = SOME rs /\
  eval_operand opr t = SOME roT /\ eval_operand opm t = SOME rs /\
  exec_delegatecall inst s (gas:bytes32) (addr:bytes32)
    (off:bytes32) (sz:bytes32) (ro:bytes32) (rs:bytes32) = OK post /\
  exec_delegatecall inst t gas addr (offT:bytes32) sz (roT:bytes32) rs = OK post' /\
  post.vs_returndata = post'.vs_returndata /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_outcomes = t.vs_outcomes /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  relocation_taint_le R tn un /\
  (!a b. next a b /\ w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
     b = w2n roT + (a-w2n ro)) /\
  (!a b. next a b /\ ~(w2n ro <= a /\
     a < w2n ro + LENGTH (TAKE (w2n rs) post.vs_returndata)) ==> R a b) ==>
  relocation_taint_le next (step_taint inst s post tn) (step_taint inst t post' un)
Proof
  strip_tac >>
  `(adopt_guard s.vs_call_ctx.cc_static s post (HD s.vs_outcomes).co_success) <=>
    (adopt_guard t.vs_call_ctx.cc_static t post' (HD t.vs_outcomes).co_success)` by
    (dxrule delegate_success_envelope >> strip_tac >>
     dxrule delegate_success_envelope >> strip_tac >>
     qmatch_asmsub_abbrev_tac `consume_call_outcome rq _ _ s = _` >>
     qmatch_asmsub_abbrev_tac `consume_call_outcome rt _ _ t = _` >>
     `rq.cr_kind = rt.cr_kind /\ rq.cr_value = rt.cr_value /\
      rq.cr_target = rt.cr_target /\ rq.cr_data = rt.cr_data` by
       simp[Abbr `rq`, Abbr `rt`, venom_call_request_def] >>
     `s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static` by simp[] >>
     drule_all ld_call_consume_adoption_test >>
     simp[update_var_def, Excl "consume_call_outcome_eq"]) >>
  dxrule delegate_execution_fields >> strip_tac >>
  dxrule delegate_execution_fields >> strip_tac >>
  `out' = out` by fs[] >> gvs[] >>
  `step_taint inst s post tn =
    tn with <|t_mem := tn.t_mem DIFF range_bytes (step_writes inst s post);
              t_var := tn.t_var |+ (out,{});
      t_stor := if (adopt_guard s.vs_call_ctx.cc_static s post (HD s.vs_outcomes).co_success) then {} else tn.t_stor;
      t_trans := if (adopt_guard s.vs_call_ctx.cc_static s post (HD s.vs_outcomes).co_success) then {} else tn.t_trans|>` by
    (irule delegate_taint >> simp[] >> metis_tac[]) >>
  `step_taint inst t post' un =
    un with <|t_mem := un.t_mem DIFF range_bytes (step_writes inst t post');
              t_var := un.t_var |+ (out,{});
      t_stor := if (adopt_guard t.vs_call_ctx.cc_static t post' (HD t.vs_outcomes).co_success) then {} else un.t_stor;
      t_trans := if (adopt_guard t.vs_call_ctx.cc_static t post' (HD t.vs_outcomes).co_success) then {} else un.t_trans|>` by
    (irule delegate_taint >> simp[] >> metis_tac[]) >>
  `LENGTH (TAKE (w2n rs) post'.vs_returndata) =
    MIN (w2n rs) (LENGTH post'.vs_returndata)` by
    simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  gvs[] >> fs[relocation_taint_le_def] >>
  simp[relocation_taint_le_def] >> conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
           memory_range_of_operands_def, range_bytes_def, demand_taint_def] >>
      qpat_x_assum `demand_taint _ _ _` mp_tac >>
      qpat_x_assum `!a b. _ ==> b = _` mp_tac >>
      qpat_x_assum `!a b. _ ==> R a b` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[demand_taint_def, LENGTH_TAKE] >> rpt strip_tac >>
      `~(w2n ro <= a /\ a < w2n ro + MIN (w2n rs) (LENGTH post'.vs_returndata))` by
        (strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
      metis_tac[]) >>
  conj_tac
  >- (simp[op_taint_def, FLOOKUP_UPDATE] >> rpt gen_tac >>
      IF_CASES_TAC >> simp[] >> fs[op_taint_def]) >>
  IF_CASES_TAC >> simp[]
QED

Theorem delegate_base_envelope[local]:
  inst.inst_opcode = DELEGATECALL /\ step_inst_base inst s = OK post ==>
  ?opg opa opd opn opr opm gas addr off sz ro rs.
    inst.inst_operands = [opg;opa;opd;opn;opr;opm] /\
    eval_operand opg s = SOME gas /\ eval_operand opa s = SOME addr /\
    eval_operand opd s = SOME off /\ eval_operand opn s = SOME sz /\
    eval_operand opr s = SOME ro /\ eval_operand opm s = SOME rs /\
    exec_delegatecall inst s gas addr off sz ro rs = OK post
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem concretize_delegate_local_complete_headroom_static:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ (o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0) /\
  EVERY wf_function C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ layout_cut_safe D lo ncut vs0 C q /\ callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  (ctx_has_dalloca C ==>
     ?eom. max_live_eom C' = SOME eom /\ eom <= w2n vs0.vs_initial_fmp) /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  (~ctx_has_dalloca C ==> resolved_complete (EL c (q0::qs)) ((rp,rv)::anns)) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  inst.inst_opcode = DELEGATECALL ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
        (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >> drule_all joint_trace_edge_at >> strip_tac >> gnvs[] >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by metis_tac[layout_cut_safe_ptr_edge, layout_cut_safe_ptr_at, layout_cut_safe_ptr_cfg] >>
  `step_inst_base inst s = OK post` by
    (qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
     simp[joint_transition_ordinary, step_inst_def]) >>
  drule_all delegate_base_envelope >> strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!op. MEM op [opg;opa;opn;opm] ==>
    eval_operand op s = eval_operand op t` by suspend "scalar" >>
  `MEM (w2n off,w2n sz) (source_memory_read_ranges inst s)` by
    gvs[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  `?offT. eval_operand opd t = SOME offT /\
     (!i. i < w2n sz /\ w2n off+i NOTIN tn.t_mem ==>
       joint_relocation_demand lo (concretize_positions C') q0 es qs c
         (w2n off+i) (w2n offT+i))` by
    (irule concretize_read_demand_geometry_headroom_static >> simp[] >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
     simp[mem_read_ops_def] >> metis_tac[]) >>
  `read_memory (w2n off) (w2n sz) s = read_memory (w2n offT) (w2n sz) t` by
    (irule concretize_read_memory_bytes >> rpt strip_tac >>
     `w2n off+i NOTIN tn.t_mem` by
       (gvs[taint_ok_def, about_to_revert_def] >>
        first_x_assum (qspecl_then [`w2n off`,`w2n sz`,`w2n off+i`] mp_tac) >>
        simp[] >> fs[]) >>
     drule local_rel_demand >> simp[frameRelocationDemandTheory.demand_agree_def] >>
     metis_tac[]) >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
     (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
     (s.vs_transient s.vs_call_ctx.cc_address)` by
    (`active_inst fn inst s` by
       (fs[joint_config_reachable_def] >>
         metis_tac[joint_origin_history_projection,
           frameHistoryDefinitionsTheory.frame_history_active]) >>
     `gas_cut ncut vs0 s` by
       metis_tac[layout_cut_safe_edge_frame, layout_cut_safe_frame,
                 layout_cut_safe_frame_cfg] >>
     `taint_within_upto D ncut C vs0` by fs[layout_cut_safe_def] >>
     `inst.inst_opcode <> INVOKE` by simp[] >>
     `step_inst 0 C inst s = OK post` by
       gvs[venomExecSemanticsTheory.step_inst_non_invoke] >>
     `LENGTH s.vs_requests < LENGTH post.vs_requests` by
       (drule delegate_success_envelope >> strip_tac >>
        qpat_x_assum `consume_call_outcome _ _ _ _ = _` mp_tac >>
        simp[consume_call_outcome_def, record_request_def, computed_precompile_def,
             venom_call_request_def, update_var_def, pairTheory.UNCURRY,
             Excl "consume_call_outcome_eq"] >> strip_tac >>
        gvs[update_var_def]) >>
     drule_all taint_within_upto_request >> simp[]) >>
  `post.vs_allocas = s.vs_allocas` by metis_tac[delegate_execution_fields] >>
  `?roT. eval_operand opr t = SOME roT /\
    (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
      w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
      b = w2n roT+(a-w2n ro)) /\
    (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
      ~(w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata)) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a b /\
      ~(w2n roT <= b /\ b < w2n roT+LENGTH (TAKE (w2n rs) post.vs_returndata)))`
    by suspend "output" >>
  `?tpost. exec_delegatecall inst t gas addr offT sz roT rs = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
        (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_env post tpost /\ relocation_reader_context post tpost` by
    (irule concretize_delegate_local_execution >> simp[] >>
     (conj_tac >- (qexists_tac `fn` >> simp[])) >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`off`,`ro`] >> fs[] >> metis_tac[]) >>
  qexists_tac `tpost` >> asm_rewrite_tac[] >>
  conj_tac >- suspend "step" >>
  `post.vs_returndata = tpost.vs_returndata` by
    (fs[local_rel_def, concretize_local_obs_def, dead_result_rel_def] >>
     irule listTheory.LIST_EQ >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx /\ s.vs_outcomes = t.vs_outcomes` by
    fs[relocation_env_def, concretize_supplement_def] >>
  irule concretize_delegate_taint_order >> simp[] >>
  goal_assum (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  fs[MEM] >> metis_tac[]
QED
Resume concretize_delegate_local_complete_headroom_static[scalar]:
  rpt strip_tac >>
  `!v. op = Var v ==> FLOOKUP rv v = NONE` by
    (rpt strip_tac >> spose_not_then assume_tac >>
     `v IN fn_pv P fn` by metis_tac[] >>
     `ptr_use_ok P (fn_pv P fn) inst` by metis_tac[fn_ptr_ok_def] >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
         mem_write_ops_def, mem_read_ops_def] >>
     qpat_x_assum `!v. _ ==> _` (qspec_then `v` mp_tac) >>
     Cases_on `opd = Var v` >> gvs[] >>
     Cases_on `opr = Var v` >> gvs[] >>
     Cases_on `opg = Var v` >> gvs[] >>
     Cases_on `opa = Var v` >> gvs[] >>
     Cases_on `opn = Var v` >> gvs[] >>
     Cases_on `opm = Var v` >> gvs[] >> rpt strip_tac >> gvs[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) disciplined_scalar_operand >>
  disch_then irule >> simp[] >>
  (conj_tac >- metis_tac[]) >> (conj_tac >- metis_tac[]) >>
  qexists_tac `inst` >> simp[] >> fs[] >> metis_tac[]
QED
Resume concretize_delegate_local_complete_headroom_static[output]:
  `?roT. eval_operand opr t = SOME roT /\
    (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
      w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata) ==>
      w2n roT <= b /\ b < w2n roT+LENGTH (TAKE (w2n rs) post.vs_returndata) /\
      a-w2n ro = b-w2n roT) /\
    (!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b /\
      ~(w2n ro <= a /\ a < w2n ro+LENGTH (TAKE (w2n rs) post.vs_returndata)) ==>
      joint_relocation_demand lo (concretize_positions C') q0 es qs c a b /\
      ~(w2n roT <= b /\ b < w2n roT+LENGTH (TAKE (w2n rs) post.vs_returndata)))` by
    (irule concretize_clean_write_geometry_headroom_static >> simp[] >>
     goal_assum (drule_at (Pat `layout_cut_safe _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `local_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `fn_ptr_ok _ _`)) >>
     goal_assum (drule_at (Pat `lifetime_ok _ _ _`)) >>
     goal_assum (drule_at (Pat `resolved_config_ok _ _ _`)) >>
     goal_assum (drule_at (Pat `callee_first _ _`)) >>
     goal_assum (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >> simp[] >>
     simp[mem_write_ops_def, source_memory_write_ranges_def,
       memory_range_of_operands_def, step_writes_def, LENGTH_TAKE] >>
     fs[] >> simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF]) >>
  qexists_tac `roT` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!a b. _ ==> _ /\ _ /\ _`
        (qspecl_then [`a`,`b`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
      pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
      pop_assum mp_tac >> pop_assum mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qpat_x_assum `!a b. _ /\ ~_ ==> _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  metis_tac[]
QED
Resume concretize_delegate_local_complete_headroom_static[step]:
  qpat_x_assum `!op. MEM op _ ==> _` mp_tac >> simp[MEM] >> strip_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >> fs[] >> simp[]
QED
Finalise concretize_delegate_local_complete_headroom_static

Theorem concretize_delegate_local_complete:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\
  vs0.vs_allocas = FEMPTY /\ layout_cut_safe D lo ncut vs0 C q /\ callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  (ctx_has_dalloca C ==>
     ?eom. max_live_eom C' = SOME eom /\ eom <= w2n vs0.vs_initial_fmp) /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  (~ctx_has_dalloca C ==> resolved_complete (EL c (q0::qs)) ((rp,rv)::anns)) /\
  lifetime_ok n (birth::ids) (JointConfig stk PG G tn fn inst s oms om hs h) /\
  ~joint_read_exempt (EL c (q0::qs)) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    concretize_local_obs s t /\
  concretize_supplement D tn s t /\
  relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un /\
  inst.inst_opcode = DELEGATECALL ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk))
        (origin_set rv inst.inst_outputs NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv inst.inst_outputs NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      concretize_local_obs post tpost /\
    concretize_supplement D (step_taint inst s post tn) post tpost /\
    relocation_taint_le (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  rpt gen_tac >> mp_tac (SPEC_ALL concretize_delegate_local_complete_headroom_static) >>
  pure_rewrite_tac[o1PassContractTheory.o1_run_state_ok_def] >>
  tautLib.TAUT_TAC
QED
