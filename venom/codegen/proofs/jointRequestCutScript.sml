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
  frameJointRevert frameJointTrace frameJointTransition contextCodegenRel
  staticAbortDefs staticShadowDefs staticShadowForbidden calleeTransport
  oracleExecProps dftGasRequestObservation opcodeClass fnRunFields venomInstProofs1
  venomExecProofs venomInstProofs venomExecSemantics venomCallOracleDefs
  extCallOracle venomWf venomState venomInst list rich_list arithmetic
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
    t.vs_requests = s.vs_requests
Proof
  Induct >> simp[pack_dret_dynamic_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[pack_dret_dynamic_def] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def]
QED

Theorem step_inst_intret_requests[local]:
  step_inst fuel ctx inst s = IntRet ret t ==> t.vs_requests = s.vs_requests
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
