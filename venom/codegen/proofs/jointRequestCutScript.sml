(* Joint-trace facts for a trace that ends at an external call or create:
   every configuration on it is outside a revert forwarding and outside a
   static-abort prefix, and the requests grow along it.

   TOP-LEVEL:
     joint_trace_nonforward_endpoint - no earlier revert forwarding
     joint_trace_call_not_static_prefix - no earlier static-abort prefix
     joint_trace_requests_prefix - requests grow along the trace
     step_inst_request_outcomes - a recording step consumes one outcome
 *)
Theory jointRequestCut
Ancestors
  frameJointRevert frameJointTrace frameJointTransition frameRawProjection
  contextCodegenRel
  staticAbortDefs staticShadowDefs staticShadowForbidden calleeTransport
  oracleExecProps dftGasRequestObservation opcodeClass fnRunFields venomInstProofs1
  venomExecProofs venomInstProofs venomExecSemantics venomCallOracleDefs
  extCallOracle venomWf venomState venomInst list rich_list arithmetic
  frameAllocationOwnership frameOriginHistory frameOriginReachable
  fmpStageBlockSimCode ptrSafeRun concretizePtrCoverageStaticMemReachability
  concretizePtrChronologicalHistory concretizeLayoutRequestRelations
Libs
  stepInstBaseLib

(* ===== Revert forwarding ===== *)

Theorem joint_revert_suffix_opcode:
  ALL_DISTINCT (fn_labels fn) /\
  joint_revert_suffix fn bb i r
    (JointConfig stk PG G tn current inst s oms om hs h) /\
  active_inst current inst s ==>
  MEM inst.inst_opcode [RETURNDATACOPY; ASSIGN; REVERT]
Proof
  rw[joint_revert_suffix_def] >>
  drule_all forwarding_active_lookup >> strip_tac >>
  gvs[revert_forward_pair_def] >>
  Cases_on `s.vs_inst_idx = i` >> gvs[] >>
  Cases_on `s.vs_inst_idx = r` >> gvs[] >>
  `i < s.vs_inst_idx /\ s.vs_inst_idx < r` by decide_tac >>
  metis_tac[]
QED

(* The GAS case of frameJointRevert, for any endpoint opcode a revert
   forwarding never holds. *)
Theorem joint_trace_nonforward_endpoint:
  joint_trace vs0 C q0 es qs
    (JointConfig stk PG G tn lastfn lastinst laststate oms om hs h) /\
  k <= LENGTH es /\
  EL k (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn inst s oms0 om0 hs0 h0 /\
  ALL_DISTINCT (fn_labels fn) /\
  active_inst lastfn lastinst laststate /\
  ~MEM lastinst.inst_opcode [RETURNDATACOPY; ASSIGN; REVERT] ==>
  ~in_revert_forward fn s
Proof
  strip_tac >> spose_not_then mp_tac >>
  rewrite_tac[in_revert_forward_def, revert_forward_at_def] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `?start stop. joint_revert_suffix fn bb start stop (EL k (q0::qs))` by
    (simp[joint_revert_suffix_def] >>
     gvs[revert_forward_pair_def] >> metis_tac[LESS_EQ_REFL, LESS_IMP_LESS_OR_EQ]) >>
  `EL (LENGTH es) (q0::qs) =
    JointConfig stk PG G tn lastfn lastinst laststate oms om hs h` by
    metis_tac[joint_trace_endpoint] >>
  mp_tac (Q.INST [`j` |-> `LENGTH es`, `k` |-> `k`,
    `i` |-> `start`, `r` |-> `stop`, `fn` |-> `fn`, `bb` |-> `bb`,
    `q` |-> `JointConfig stk PG G tn lastfn lastinst laststate oms om hs h`]
    (SPEC_ALL joint_trace_revert_suffix)) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  simp[] >> strip_tac >>
  `lastfn = fn` by fs[joint_revert_suffix_def] >> gvs[] >>
  drule_all joint_revert_suffix_opcode >> simp[]
QED

(* ===== Static-abort prefixes ===== *)

Theorem static_write_no_ok:
  MEM inst.inst_opcode [SSTORE; TSTORE; LOG] /\ s.vs_call_ctx.cc_static ==>
  step_inst fuel ctx inst s <> OK t
Proof
  strip_tac >> fs[]
  >- (simp[step_inst_non_invoke] >> with_opcode_clause simp >>
      Cases_on `eval_operands inst.inst_operands s` >>
      gvs[exec_write2_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[eval_operands_def])
  >- (simp[step_inst_non_invoke] >> with_opcode_clause simp >>
      Cases_on `eval_operands inst.inst_operands s` >>
      gvs[exec_write2_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[eval_operands_def])
  >> `static_shadow_result_rel (step_inst_base inst s) (Error "")` by
       (irule static_shadow_forbidden >> simp[]) >>
  gvs[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> gvs[static_shadow_result_rel_def]
QED

Theorem static_abort_pair_suc[local]:
  static_abort_pair bb i r /\ i < r ==> static_abort_pair bb (SUC i) r
Proof
  rewrite_tac[static_abort_pair_def] >> strip_tac >>
  rpt conj_tac >> TRY decide_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`k`, `inst`] mp_tac) >> simp[]
QED

(* Inside a static-abort prefix only the ordinary edge leaves a
   configuration, and it stays inside the prefix. *)
Theorem joint_static_prefix_step:
  ALL_DISTINCT (fn_labels fn) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  static_abort_pair bb s.vs_inst_idx r /\ s.vs_call_ctx.cc_static /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) ev q' ==>
  ?stk' PG' G' tn' inst' s' oms' om' hs' h'.
    q' = JointConfig stk' PG' G' tn' fn inst' s' oms' om' hs' h' /\
    lookup_block s'.vs_current_bb fn.fn_blocks = SOME bb /\
    static_abort_pair bb s'.vs_inst_idx r /\ s'.vs_call_ctx.cc_static
Proof
  strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[] >>
  drule_all forwarding_active_lookup >> strip_tac >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   (s.vs_inst_idx = r ==> MEM inst.inst_opcode [SSTORE; TSTORE; LOG])` by
    (qpat_x_assum `static_abort_pair _ _ _` mp_tac >>
     rewrite_tac[static_abort_pair_def] >> strip_tac >>
     Cases_on `s.vs_inst_idx = r`
     >- (gvs[get_instruction_def] >> gvs[is_terminator_def]) >>
     `s.vs_inst_idx < r` by decide_tac >>
     first_x_assum (qspecl_then [`s.vs_inst_idx`, `inst`] mp_tac) >> simp[]) >>
  gvs[]
  >- (Cases_on `s.vs_inst_idx = r`
      >- (`MEM inst.inst_opcode [SSTORE; TSTORE; LOG]` by gvs[] >>
          metis_tac[static_write_no_ok]) >>
      `s.vs_inst_idx < r` by fs[static_abort_pair_def] >>
      `s'.vs_current_bb = s.vs_current_bb` by
        metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
      `s'.vs_call_ctx = s.vs_call_ctx` by
        metis_tac[step_inst_ok_preserves_call_ctx] >>
      simp[] >> irule static_abort_pair_suc >> simp[]) >>
  TRY (fs[decode_invoke_def, AllCaseEqs()] >> NO_TAC) >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke] >> strip_tac >>
  drule step_inst_base_no_intret >> simp[]
QED

Theorem joint_trace_static_prefix:
  !j k. joint_trace vs0 C q0 es qs q /\ k <= j /\ j <= LENGTH es /\
  ALL_DISTINCT (fn_labels fn) /\
  EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  static_abort_pair bb s.vs_inst_idx r /\ s.vs_call_ctx.cc_static ==>
  ?stk' PG' G' tn' inst' s' oms' om' hs' h'.
    EL j (q0::qs) = JointConfig stk' PG' G' tn' fn inst' s' oms' om' hs' h' /\
    lookup_block s'.vs_current_bb fn.fn_blocks = SOME bb /\
    static_abort_pair bb s'.vs_inst_idx r /\ s'.vs_call_ctx.cc_static
Proof
  Induct >> rpt strip_tac >- (gvs[] >> metis_tac[]) >>
  Cases_on `k = SUC j` >- (gvs[] >> metis_tac[]) >>
  `k <= j /\ j < LENGTH es` by decide_tac >>
  last_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  drule joint_trace_edge_at >> disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >>
  drule_at (Pat `joint_transition _ _ _ _`) joint_static_prefix_step >>
  simp[] >> disch_then drule_all >> simp[]
QED

Theorem joint_trace_call_not_static_prefix:
  joint_trace vs0 C q0 es qs
    (JointConfig stk PG G tn lastfn lastinst laststate oms om hs h) /\
  k <= LENGTH es /\
  EL k (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn inst s oms0 om0 hs0 h0 /\
  ALL_DISTINCT (fn_labels fn) /\
  active_inst lastfn lastinst laststate /\
  MEM lastinst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  ~in_static_abort_prefix fn s
Proof
  rewrite_tac[in_static_abort_prefix_def, static_abort_at_def] >>
  strip_tac >> spose_not_then strip_assume_tac >>
  `EL (LENGTH es) (q0::qs) =
    JointConfig stk PG G tn lastfn lastinst laststate oms om hs h` by
    metis_tac[joint_trace_endpoint] >>
  `LENGTH es <= LENGTH es` by simp[] >>
  qspecl_then [`LENGTH es`, `k`] (fn th => drule_all (GEN_ALL th))
    joint_trace_static_prefix >> strip_tac >> gvs[] >>
  drule_all forwarding_active_lookup >> strip_tac >>
  qpat_x_assum `static_abort_pair _ _ _` mp_tac >>
  rewrite_tac[static_abort_pair_def] >> strip_tac >>
  Cases_on `laststate.vs_inst_idx = j` >> gvs[get_instruction_def] >>
  `laststate.vs_inst_idx < j` by decide_tac >>
  first_x_assum (qspec_then `laststate.vs_inst_idx` mp_tac) >>
  gvs[get_instruction_def]
QED

(* ===== Requests along the trace ===== *)

Theorem pack_dret_dynamic_requests[local]:
  !pairs cursor s ptrs fc t.
    pack_dret_dynamic cursor pairs s = (ptrs,fc,t) ==>
    t.vs_requests = s.vs_requests /\ t.vs_outcomes = s.vs_outcomes
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem step_inst_intret_requests:
  step_inst fuel ctx inst s = IntRet ret t ==>
  t.vs_requests = s.vs_requests /\ t.vs_outcomes = s.vs_outcomes
Proof
  disch_tac >>
  gvs[step_inst_def, AllCaseEqs()] >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[] >>
  drule pack_dret_dynamic_requests >> simp[]
QED

Theorem joint_transition_requests_prefix:
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' s' oms' om' hs' h') ==>
  s.vs_requests <<= s'.vs_requests
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[]
  >- metis_tac[step_inst_requests_prefix]
  >- (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      drule_all step_inst_requests_prefix >>
      gvs[enters_block_def] >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o Q.AP_TERM `\u. u.vs_requests`) >> simp[])
  >- (drule setup_callee_oracle >> gvs[enters_block_def] >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o Q.AP_TERM `\u. u.vs_requests`) >> simp[]) >>
  drule bind_outputs_oracle >> drule step_inst_intret_requests >> simp[]
QED

Theorem ptr_chrono_step_requests_prefix:
  !C a b. ptr_chrono_step C a b ==> a.po_state.vs_requests <<= b.po_state.vs_requests
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> simp[ptr_observe_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- metis_tac[step_inst_requests_prefix]
  >- (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      metis_tac[step_inst_requests_prefix, enters_block_requests])
  >- (drule setup_callee_oracle >> drule enters_block_requests >> simp[]) >>
  drule bind_outputs_oracle >> drule step_inst_intret_requests >> simp[]
QED

Theorem ptr_chrono_history_requests_le:
  !vs C h a. ptr_chrono_history vs C h a ==>
    EVERY (\b. LENGTH b.po_state.vs_requests <= LENGTH a.po_state.vs_requests) h
Proof
  ho_match_mp_tac ptr_chrono_history_ind >> conj_tac
  >- simp[] >>
  rpt gen_tac >> strip_tac >> simp[EVERY_APPEND] >>
  drule ptr_chrono_step_requests_prefix >>
  simp[IS_PREFIX_APPEND] >> strip_tac >>
  gvs[EVERY_MEM] >> qx_gen_tac `b` >> strip_tac >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >> decide_tac
QED

Theorem joint_trace_requests_prefix:
  !j k stk' PG' G' tn' fn' inst' t oms' om' hs' h'.
  joint_trace vs0 C q0 es qs q /\ k <= j /\ j <= LENGTH es /\
  EL k (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL j (q0::qs) = JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h' ==>
  s.vs_requests <<= t.vs_requests
Proof
  Induct >> rpt strip_tac >- gvs[] >>
  Cases_on `k = SUC j` >- gvs[] >>
  `k <= j /\ j < LENGTH es` by decide_tac >>
  Cases_on `EL j (q0::qs)` >>
  rename1 `EL j (q0::qs) = JointConfig mstk mPG mG mtn mfn minst mid momss mom mhs mh` >>
  `s.vs_requests <<= mid.vs_requests` by
    (last_x_assum (qspecl_then [`k`, `mstk`, `mPG`, `mG`, `mtn`, `mfn`,
       `minst`, `mid`, `momss`, `mom`, `mhs`, `mh`] mp_tac) >> simp[]) >>
  drule joint_trace_edge_at >> disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  drule joint_transition_requests_prefix >> metis_tac[IS_PREFIX_TRANS]
QED

(* ===== One recording step ===== *)

Theorem step_inst_request_outcomes:
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK t /\
  LENGTH s.vs_requests < LENGTH t.vs_requests ==>
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  t.vs_outcomes = TL s.vs_outcomes
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (gvs[step_inst_non_invoke] >> with_opcode_clause gvs >>
      gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
          consume_call_outcome_def, consume_create_outcome_def,
          take_outcome_def, record_request_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[take_outcome_def, AllCaseEqs()]) >>
  gvs[step_inst_non_invoke] >> drule_all step_inst_base_oracle >>
  strip_tac >> gvs[]
QED

Theorem recording_step_appends_one:
  inst.inst_opcode <> INVOKE /\ step_inst fuel ctx inst s = OK post /\
  LENGTH s.vs_requests < LENGTH post.vs_requests ==>
  ?rq. post.vs_requests = s.vs_requests ++ [rq] /\
    rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient
Proof
  strip_tac >> drule_all step_inst_request_outcomes >> strip_tac >>
  gvs[step_inst_non_invoke] >> with_opcode_clause gvs >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
      consume_call_outcome_def, consume_create_outcome_def,
      record_request_def, update_var_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs()] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[venom_call_request_def, venom_create_request_def]
QED

(* The first edge out of the cut records exactly one request. Nested calls
   and returns transport the existing request list across their boundary. *)
Theorem joint_transition_request_crossing[local]:
  joint_transition ctx (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') /\
  LENGTH s.vs_requests <= k /\ k < LENGTH t.vs_requests ==>
  ?fuel post.
    ev = SOME (OriginOrdinary fuel post) /\ inst.inst_opcode <> INVOKE /\
    LENGTH s.vs_requests = k /\ step_inst fuel ctx inst s = OK post /\
    post.vs_requests = t.vs_requests
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[]
  >- (`LENGTH s.vs_requests < LENGTH s'.vs_requests` by decide_tac >>
      drule_all recording_step_appends_one >> strip_tac >> fs[] >> decide_tac)
  >- (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      `t.vs_requests = s'.vs_requests` by
        (gvs[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
         disch_then (mp_tac o Q.AP_TERM `\u. u.vs_requests`) >> simp[]) >>
      `LENGTH s.vs_requests < LENGTH s'.vs_requests` by (fs[] >> decide_tac) >>
      drule_all step_inst_request_outcomes >>
      disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
      gvs[is_terminator_def])
  >- (drule setup_callee_oracle >> gvs[enters_block_def] >>
      drule eval_phis_only_updates_vs_vars >>
      disch_then (mp_tac o Q.AP_TERM `\u. u.vs_requests`) >>
      rpt strip_tac >> fs[] >> decide_tac) >>
  drule bind_outputs_oracle >> drule step_inst_intret_requests >>
  rpt strip_tac >> fs[] >> decide_tac
QED

(* A retained trace that has exited the cut contains the actual recording
   edge. The index identifies its occurrence even if configurations repeat. *)
Theorem joint_trace_request_crossing:
  EVERY wf_function ctx.ctx_functions /\
  joint_trace vs0 ctx q0 evs qs
    (JointConfig stk PG G tn fn inst t oms om hs h) /\
  LENGTH vs0.vs_requests <= k /\ k < LENGTH t.vs_requests ==>
  ?j fn0 inst0 s fuel post.
    j < LENGTH evs /\ EL j evs = SOME (OriginOrdinary fuel post) /\
    (?stk0 PG0 G0 tn0 oms0 om0 hs0 h0.
      EL j (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn0 inst0 s oms0 om0 hs0 h0) /\
    raw_reachable vs0 ctx fn0 inst0 s /\ inst0.inst_opcode <> INVOKE /\
    LENGTH s.vs_requests = k /\ step_inst fuel ctx inst0 s = OK post /\
    k < LENGTH post.vs_requests /\ post.vs_requests <<= t.vs_requests
Proof
  strip_tac >>
  qabbrev_tac `rq_count = \q. case q of
    JointConfig _ _ _ _ _ _ s _ _ _ _ => LENGTH s.vs_requests` >>
  `rq_count q0 = LENGTH vs0.vs_requests` by
    (qpat_assum `joint_trace _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [joint_trace_def]) >>
     qpat_x_assum `joint_initial _ _ _` mp_tac >>
     simp[Once joint_initial_cases, Abbr `rq_count`] >> rpt strip_tac >>
     gvs[enters_block_def] >> drule eval_phis_only_updates_vs_vars >>
     disch_then (mp_tac o Q.AP_TERM `\u. u.vs_requests`) >> simp[]) >>
  `?n. n <= LENGTH evs /\ k < rq_count (EL n (q0::qs)) /\
       !m. m < n ==> rq_count (EL m (q0::qs)) <= k` by
    (qexists_tac `LEAST n. n <= LENGTH evs /\ k < rq_count (EL n (q0::qs))` >>
     numLib.LEAST_ELIM_TAC >> conj_tac
     >- (qexists_tac `LENGTH evs` >>
         drule joint_trace_endpoint >> simp[Abbr `rq_count`]) >>
     rpt strip_tac >>
     first_x_assum (qspec_then `m` mp_tac) >> simp[] >> decide_tac) >>
  Cases_on `n` >- gvs[] >>
  rename1 `SUC n <= LENGTH evs` >>
  `n < LENGTH evs /\ rq_count (EL n (q0::qs)) <= k` by simp[] >>
  drule_all joint_trace_edge_at >> strip_tac >>
  qpat_x_assum `rq_count (EL n _) <= k` mp_tac >>
  qpat_x_assum `k < rq_count (EL (SUC n) _)` mp_tac >>
  Cases_on `EL n (q0::qs)` >> Cases_on `EL (SUC n) (q0::qs)` >>
  simp[Abbr `rq_count`] >> rpt strip_tac >>
  drule_all joint_transition_request_crossing >> strip_tac >>
  imp_res_tac joint_config_raw >>
  `EL (LENGTH evs) (q0::qs) = JointConfig stk PG G tn fn inst t oms om hs h` by
    metis_tac[joint_trace_endpoint] >>
  `SUC n <= LENGTH evs` by decide_tac >>
  rename1 `EL (SUC n) (q0::qs) =
    JointConfig nstk nPG nG ntn nfn ninst next noms nom nhs nh` >>
  `post.vs_requests <<= t.vs_requests` by
    (mp_tac (Q.INST [`C` |-> `ctx`, `es` |-> `evs`,
      `q` |-> `JointConfig stk PG G tn fn inst t oms om hs h`,
      `j` |-> `LENGTH (evs:origin_event option list)`, `k` |-> `SUC n`,
      `stk` |-> `nstk`, `PG` |-> `nPG`, `G` |-> `nG`, `tn` |-> `ntn`,
      `fn` |-> `nfn`, `inst` |-> `ninst`, `s` |-> `next`,
      `oms` |-> `noms`, `om` |-> `nom`, `hs` |-> `nhs`, `h` |-> `nh`,
      `stk'` |-> `stk`, `PG'` |-> `PG`, `G'` |-> `G`, `tn'` |-> `tn`,
      `fn'` |-> `fn`, `inst'` |-> `inst`, `t` |-> `t`,
      `oms'` |-> `oms`, `om'` |-> `om`, `hs'` |-> `hs`, `h'` |-> `h`]
      (SPEC_ALL joint_trace_requests_prefix)) >> simp[]) >>
  qexists_tac `n` >> gvs[] >> metis_tac[]
QED

(* A fixed initial state determines the execution projection. *)

Theorem cut_joint_active_unique[local]:
  EVERY wf_function C.ctx_functions /\
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  active_inst fn inst s /\ active_inst fn inst' s ==>
  inst = inst'
Proof
  simp[joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  drule frame_reachable_functions_member >> strip_tac >>
  irule active_inst_unique >> qexistsl [`fn`, `s`] >>
  gvs[EVERY_MEM, wf_function_def] >> metis_tac[]
QED

Theorem cut_terminator_not_invoke[local]:
  is_terminator op ==> op <> INVOKE
Proof
  Cases_on `op = INVOKE` >> simp[is_terminator_def]
QED

(* The supplied step fuel is recorded in the history, but it cannot
   change the execution components of a joint edge. *)
Theorem cut_joint_transition_unique[local]:
  EVERY wf_function C.ctx_functions /\
  MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) stk =
  MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) stk' /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) ev q /\
  joint_transition C (JointConfig stk' PG' G' tn' fn inst s oms' om' hs' h') ev' q' /\
  joint_config_reachable vs0 C q ==>
  (case (q,q') of
    (JointConfig a _ _ _ f i u _ _ _ _,
     JointConfig b _ _ _ g j v _ _ _ _) =>
       MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) a = MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) b /\
       f = g /\ i = j /\ u = v)
Proof
  strip_tac >>
  qpat_x_assum `joint_transition C _ ev q` mp_tac >>
  rewrite_tac[Once joint_transition_cases] >> strip_tac >> gvs[] >>
  qpat_x_assum `joint_transition C _ ev' q'` mp_tac >>
  rewrite_tac[Once joint_transition_cases] >>
  rpt strip_tac >> gvs[is_terminator_def] >>
  imp_res_tac step_inst_intret_not_invoke >>
  imp_res_tac cut_terminator_not_invoke >>
  gvs[step_inst_non_invoke] >>
  gvs[enters_block_def] >>
  metis_tac[cut_joint_active_unique]
QED

Theorem cut_joint_initial_unique[local]:
  EVERY wf_function C.ctx_functions /\
  joint_initial vs0 C q /\ joint_initial vs0 C r ==>
  (case (q,r) of
    (JointConfig a _ _ _ f i u _ _ _ _,
     JointConfig b _ _ _ g j v _ _ _ _) =>
       MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) a =
       MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) b /\
       f = g /\ i = j /\ u = v)
Proof
  strip_tac >>
  `joint_config_reachable vs0 C q` by metis_tac[joint_initial_reachable] >>
  qpat_x_assum `joint_initial vs0 C q` mp_tac >>
  rewrite_tac[Once joint_initial_cases] >> strip_tac >> gvs[] >>
  qpat_x_assum `joint_initial vs0 C r` mp_tac >>
  rewrite_tac[Once joint_initial_cases] >>
  rpt strip_tac >> gvs[enters_block_def] >>
  metis_tac[cut_joint_active_unique]
QED

Theorem cut_joint_trace_execution_agrees:
  !n q0 es qs q r0 fs rs r.
    EVERY wf_function C.ctx_functions /\
    joint_trace vs0 C q0 es qs q /\ joint_trace vs0 C r0 fs rs r /\
    n <= LENGTH es /\ n <= LENGTH fs ==>
    (case (EL n (q0::qs),EL n (r0::rs)) of
      (JointConfig a _ _ _ f i u _ _ _ _,
       JointConfig b _ _ _ g j v _ _ _ _) =>
         MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) a =
         MAP (\fr. (fr.cf_fn,fr.cf_inst,fr.cf_state)) b /\
         f = g /\ i = j /\ u = v)
Proof
  Induct
  >- (simp[joint_trace_def] >> rpt strip_tac >>
      mp_tac (Q.INST [`q` |-> `q0`, `r` |-> `r0`] cut_joint_initial_unique) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `n < LENGTH es /\ n < LENGTH fs` by decide_tac >>
  first_x_assum
    (qspecl_then [`q0`, `es`, `qs`, `q`, `r0`, `fs`, `rs`, `r`] mp_tac) >>
  (impl_tac >- simp[]) >>
  mp_tac (Q.INST [`ctx` |-> `C`, `q0` |-> `q0`, `es` |-> `es`, `qs` |-> `qs`,
                `q` |-> `q`, `n` |-> `n`] (SPEC_ALL joint_trace_edge_at)) >>
  mp_tac (Q.INST [`ctx` |-> `C`, `q0` |-> `r0`, `es` |-> `fs`, `qs` |-> `rs`,
                `q` |-> `r`, `n` |-> `n`] (SPEC_ALL joint_trace_edge_at)) >>
  simp[] >> rpt strip_tac >>
  Cases_on `EL n (q0::qs)` >> Cases_on `EL n (r0::rs)` >> gvs[] >>
  drule_all cut_joint_transition_unique >> simp[]
QED

Theorem raw_reachable_joint_trace:
  raw_reachable vs C fn inst s ==>
  ?q0 es qs stk PG G tn oms om hs h.
    joint_trace vs C q0 es qs (JointConfig stk PG G tn fn inst s oms om hs h)
Proof
  strip_tac >> drule ptr_raw_reachable_frame >> strip_tac >>
  drule frame_reachable_has_origins >> strip_tac >>
  drule origin_frame_has_joint_history >> strip_tac >>
  drule joint_history_trace >> metis_tac[]
QED

(* The shorter trace fixes the same recorded prefix even when reachability
   was witnessed with different step fuels. *)
Theorem joint_trace_endpoint_requests_prefix:
  EVERY wf_function C.ctx_functions /\
  joint_trace vs0 C q0 es qs (JointConfig stk PG G tn fn inst s oms om hs h) /\
  joint_trace vs0 C r0 fs rs
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') /\
  LENGTH es <= LENGTH fs ==>
  s.vs_requests <<= t.vs_requests
Proof
  strip_tac >>
  `EL (LENGTH es) (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h` by
    metis_tac[joint_trace_endpoint] >>
  `EL (LENGTH fs) (r0::rs) = JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h'` by
    metis_tac[joint_trace_endpoint] >>
  mp_tac (Q.SPECL [`LENGTH (es:origin_event option list)`, `q0`, `es`, `qs`,
     `JointConfig stk PG G tn fn inst s oms om hs h`, `r0`, `fs`, `rs`,
     `JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h'`]
     cut_joint_trace_execution_agrees) >>
  simp[] >>
  Cases_on `EL (LENGTH es) (r0::rs)` >> gvs[] >> strip_tac >>
  rename1 `EL (LENGTH es) (r0::rs) =
    JointConfig mstk mPG mG mtn mfn mi mid moms mom mhs mh` >>
  mp_tac (Q.INST [`q0` |-> `r0`, `es` |-> `fs`, `qs` |-> `rs`,
    `q` |-> `JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h'`,
    `j` |-> `LENGTH (fs:origin_event option list)`,
    `k` |-> `LENGTH (es:origin_event option list)`,
    `stk` |-> `mstk`, `PG` |-> `mPG`, `G` |-> `mG`, `tn` |-> `mtn`,
    `fn` |-> `mfn`, `inst` |-> `mi`, `s` |-> `mid`,
    `oms` |-> `moms`, `om` |-> `mom`, `hs` |-> `mhs`, `h` |-> `mh`,
    `stk'` |-> `stk'`, `PG'` |-> `PG'`, `G'` |-> `G'`, `tn'` |-> `tn'`,
    `fn'` |-> `fn'`, `inst'` |-> `inst'`, `t` |-> `t`,
    `oms'` |-> `oms'`, `om'` |-> `om'`, `hs'` |-> `hs'`, `h'` |-> `h'`]
    (SPEC_ALL joint_trace_requests_prefix)) >> simp[]
QED

Theorem raw_reachable_requests_comparable:
  EVERY wf_function C.ctx_functions /\
  raw_reachable vs0 C fn inst s /\ raw_reachable vs0 C fn' inst' t ==>
  s.vs_requests <<= t.vs_requests \/ t.vs_requests <<= s.vs_requests
Proof
  strip_tac >>
  qpat_x_assum `raw_reachable vs0 C fn inst s`
    (strip_assume_tac o MATCH_MP raw_reachable_joint_trace) >>
  qpat_x_assum `raw_reachable vs0 C fn' inst' t`
    (strip_assume_tac o MATCH_MP raw_reachable_joint_trace) >>
  Cases_on `LENGTH es <= LENGTH es'`
  >- metis_tac[joint_trace_endpoint_requests_prefix] >>
  `LENGTH es' <= LENGTH es` by decide_tac >>
  metis_tac[joint_trace_endpoint_requests_prefix]
QED

(* Once a retained trace has crossed the request cut, every reachable
   pre-cut observation occurs on that trace, with the same native state. *)
Theorem raw_reachable_request_cut_visit:
  EVERY wf_function C.ctx_functions /\
  joint_trace vs0 C q0 es qs
    (JointConfig stk PG G tn fn inst last oms om hs h) /\
  k < LENGTH last.vs_requests /\
  raw_reachable vs0 C g j s /\ LENGTH s.vs_requests <= k ==>
  ?n stk' PG' G' tn' oms' om' hs' h'.
    n < LENGTH es /\
    EL n (q0::qs) = JointConfig stk' PG' G' tn' g j s oms' om' hs' h'
Proof
  strip_tac >> dxrule raw_reachable_joint_trace >> strip_tac >>
  `LENGTH es' < LENGTH es` by
    (spose_not_then assume_tac >>
     `LENGTH es <= LENGTH es'` by decide_tac >>
     `last.vs_requests <<= s.vs_requests` by
       metis_tac[joint_trace_endpoint_requests_prefix] >>
     drule IS_PREFIX_LENGTH >> decide_tac) >>
  `EL (LENGTH es') (q0'::qs') =
      JointConfig stk' PG' G' tn' g j s oms' om' hs' h'` by
    metis_tac[joint_trace_endpoint] >>
  mp_tac (Q.SPECL
    [`LENGTH (es':origin_event option list)`, `q0'`, `es'`, `qs'`,
     `JointConfig stk' PG' G' tn' g j s oms' om' hs' h'`, `q0`, `es`, `qs`,
     `JointConfig stk PG G tn fn inst last oms om hs h`]
    cut_joint_trace_execution_agrees) >>
  impl_tac >- (simp[] >> decide_tac) >>
  Cases_on `EL (LENGTH es') (q0::qs)` >> simp[] >> strip_tac >>
  qexists_tac `LENGTH es'` >> simp[] >> metis_tac[]
QED

(* Dropping outcomes by recorded index under the append-all recorder law. *)

Theorem noninvoke_recorded_oracle_effect:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK post ==>
  (post.vs_requests = s.vs_requests /\ post.vs_outcomes = s.vs_outcomes) \/
  (?rq. post.vs_requests = s.vs_requests ++ [rq] /\
        s.vs_outcomes <> [] /\ post.vs_outcomes = TL s.vs_outcomes)
Proof
  strip_tac >>
  Cases_on `MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (gvs[step_inst_non_invoke] >> with_opcode_clause gvs >>
      gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
          consume_call_outcome_def, consume_create_outcome_def,
          take_outcome_def, update_var_def, record_request_def, AllCaseEqs()] >>
      rpt (pairarg_tac >> gvs[]) >>
      gvs[AllCaseEqs()] >> BasicProvers.EVERY_CASE_TAC >> gvs[]) >>
  gvs[step_inst_non_invoke] >> drule_all step_inst_base_oracle >>
  simp[]
QED

Theorem noninvoke_recorded_oracle_drop:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK post ==>
  LENGTH s.vs_requests <= LENGTH post.vs_requests /\
  post.vs_outcomes =
    DROP (LENGTH post.vs_requests - LENGTH s.vs_requests) s.vs_outcomes
Proof
  strip_tac >>
  drule_all noninvoke_recorded_oracle_effect >> strip_tac >> simp[] >>
  Cases_on `s.vs_outcomes` >> gvs[]
QED

Theorem enters_block_oracle:
  enters_block fn s t ==>
  t.vs_requests = s.vs_requests /\ t.vs_outcomes = s.vs_outcomes
Proof
  simp[enters_block_def] >> strip_tac >>
  drule eval_phis_only_updates_vs_vars >>
  disch_then (mp_tac o Q.AP_TERM `\u. (u.vs_requests,u.vs_outcomes)`) >> simp[]
QED

Theorem joint_transition_recorded_oracle_drop:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  joint_transition C (JointConfig stk PG G tn fn inst s oms om hs h) ev
    (JointConfig stk' PG' G' tn' fn' inst' t oms' om' hs' h') ==>
  LENGTH s.vs_requests <= LENGTH t.vs_requests /\
  t.vs_outcomes =
    DROP (LENGTH t.vs_requests - LENGTH s.vs_requests) s.vs_outcomes
Proof
  simp[Once joint_transition_cases] >> rpt strip_tac >> gvs[]
  >- (drule_all noninvoke_recorded_oracle_drop >> simp[])
  >- (drule_all noninvoke_recorded_oracle_drop >> simp[])
  >- (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      drule_all noninvoke_recorded_oracle_drop >>
      drule enters_block_oracle >> simp[])
  >- (`inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
      drule_all noninvoke_recorded_oracle_drop >>
      drule enters_block_oracle >> simp[])
  >- (drule setup_callee_oracle >> drule enters_block_oracle >> simp[])
  >- (drule setup_callee_oracle >> drule enters_block_oracle >> simp[])
  >> drule step_inst_intret_requests >> drule bind_outputs_oracle >> simp[]
QED

Theorem joint_chain_recorded_oracle_drop[local]:
  !es qs q r.
    (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
    joint_chain C q es qs r ==>
    (case (q,r) of
       (JointConfig _ _ _ _ _ _ s _ _ _ _,
        JointConfig _ _ _ _ _ _ t _ _ _ _) =>
         LENGTH s.vs_requests <= LENGTH t.vs_requests /\
         t.vs_outcomes =
           DROP (LENGTH t.vs_requests - LENGTH s.vs_requests) s.vs_outcomes)
Proof
  Induct
  >- (Cases_on `qs` >> simp[joint_chain_def] >> Cases_on `q` >> simp[]) >>
  Cases_on `qs` >> simp[joint_chain_def] >> rpt gen_tac >> strip_tac >>
  rename1 `joint_chain C middle es rest r` >>
  Cases_on `q` >> Cases_on `r` >> Cases_on `middle` >> gvs[] >>
  drule_all joint_transition_recorded_oracle_drop >> strip_tac >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  simp[DROP_DROP_T] >> decide_tac
QED

Theorem joint_trace_recorded_oracle_drop:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  joint_trace vs0 C q0 es qs (JointConfig stk PG G tn fn inst s oms om hs h) ==>
  LENGTH vs0.vs_requests <= LENGTH s.vs_requests /\
  s.vs_outcomes = DROP (LENGTH s.vs_requests - LENGTH vs0.vs_requests) vs0.vs_outcomes
Proof
  simp[joint_trace_def] >> strip_tac >>
  drule_all joint_chain_recorded_oracle_drop >>
  qpat_x_assum `joint_initial _ _ _` mp_tac >>
  simp[Once joint_initial_cases] >> strip_tac >> gvs[] >>
  drule enters_block_oracle >> simp[]
QED

Theorem raw_reachable_recorded_oracle_drop:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  raw_reachable vs C fn inst s ==>
  LENGTH vs.vs_requests <= LENGTH s.vs_requests /\
  s.vs_outcomes = DROP (LENGTH s.vs_requests - LENGTH vs.vs_requests) vs.vs_outcomes
Proof
  strip_tac >> drule raw_reachable_joint_trace >> strip_tac >>
  metis_tac[joint_trace_recorded_oracle_drop]
QED

Theorem recorded_index_same_outcomes:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  vs.vs_requests = vs0.vs_requests /\ vs.vs_outcomes = vs0.vs_outcomes /\
  raw_reachable vs C fn inst s /\ raw_reachable vs0 Ct fn' inst' t /\
  LENGTH s.vs_requests = LENGTH t.vs_requests ==>
  t.vs_outcomes = s.vs_outcomes
Proof
  strip_tac >>
  imp_res_tac raw_reachable_recorded_oracle_drop >> simp[]
QED

Theorem earlier_recorded_index_has_outcome:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  vs.vs_requests = vs0.vs_requests /\ vs.vs_outcomes = vs0.vs_outcomes /\
  raw_reachable vs C fn inst s /\ raw_reachable vs0 Ct fn' inst' t /\
  LENGTH t.vs_requests <= LENGTH s.vs_requests /\ s.vs_outcomes <> [] ==>
  t.vs_outcomes <> []
Proof
  strip_tac >>
  imp_res_tac raw_reachable_recorded_oracle_drop >>
  fs[DROP_EQ_NIL] >>
  `LENGTH vs0.vs_requests = LENGTH vs.vs_requests /\
   LENGTH vs0.vs_outcomes = LENGTH vs.vs_outcomes` by simp[] >>
  decide_tac
QED

Theorem recording_step_has_outcome:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK t /\
  LENGTH s.vs_requests < LENGTH t.vs_requests ==> s.vs_outcomes <> []
Proof
  strip_tac >> drule_all noninvoke_recorded_oracle_effect >> strip_tac >> fs[]
QED

Theorem recorded_step_within_oracle_length:
  (!rq rqs. record_request rq rqs = rqs ++ [rq]) /\
  vs.vs_requests = [] /\
  raw_reachable vs C fn inst s /\ inst.inst_opcode <> INVOKE /\
  step_inst fuel C inst s = OK t /\
  LENGTH s.vs_requests < LENGTH t.vs_requests ==>
  LENGTH s.vs_requests < LENGTH vs.vs_outcomes
Proof
  strip_tac >> drule_all recording_step_has_outcome >> strip_tac >>
  drule_all raw_reachable_recorded_oracle_drop >> strip_tac >> fs[DROP_EQ_NIL] >>
  `LENGTH vs.vs_requests = 0` by asm_rewrite_tac[LENGTH] >>
  decide_tac
QED
