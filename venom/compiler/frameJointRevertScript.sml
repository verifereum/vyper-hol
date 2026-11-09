Theory frameJointRevert
Ancestors
  frameJointDemand frameJointTransition frameJointTrace contextCodegenRel memSafeRun opcodeClass venomExecProps
  venomExecSemantics venomState venomInst ptrDiscipline list arithmetic
  frameOriginHistory frameHistoryCfg o1PassContract venomWf

Theorem forwarding_revert_no_step[local]:
  inst.inst_opcode = REVERT ==>
  step_inst fuel ctx inst s <> OK post /\
  step_inst fuel ctx inst s <> IntRet ret send
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  Cases_on `eval_operand h' s` >> simp[]
QED

Theorem forwarding_step_control[local]:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = RETURNDATACOPY) /\
  step_inst fuel ctx inst s = OK post ==>
  post.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs(),
    update_var_def, write_memory_def, write_memory_with_expansion_def,
    expand_memory_def]
QED

(* A fixed suffix witness includes the intermediate ASSIGNs, unlike the
   two-point exemption itself. *)
Definition joint_revert_suffix_def:
  joint_revert_suffix fn bb i r (JointConfig stk PG G tn current inst s oms om hs h) <=>
    current = fn /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    revert_forward_pair bb i r /\ i <= s.vs_inst_idx /\ s.vs_inst_idx <= r
End

Theorem forwarding_active_lookup[local]:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def, fn_labels_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> simp[]) >>
  gvs[get_instruction_def]
QED

Theorem forwarding_suffix_opcode[local]:
  revert_forward_pair bb i r /\ i <= k /\ k <= r /\
  get_instruction bb k = SOME inst ==>
  (k = i /\ inst.inst_opcode = RETURNDATACOPY) \/
  (i < k /\ k < r /\ inst.inst_opcode = ASSIGN) \/
  (k = r /\ inst.inst_opcode = REVERT)
Proof
  rw[revert_forward_pair_def] >>
  Cases_on `k = i` >> gvs[] >> Cases_on `k = r` >> gvs[] >>
  `i < k /\ k < r` by decide_tac >> metis_tac[]
QED

Theorem joint_revert_suffix_step:
  ALL_DISTINCT (fn_labels fn) /\ joint_revert_suffix fn bb i r q /\
  joint_transition ctx q ev q' ==>
  joint_revert_suffix fn bb i r q'
Proof
  Cases_on `q` >> simp[joint_revert_suffix_def] >> strip_tac >>
  qpat_x_assum `joint_transition _ _ _ _` mp_tac >>
  simp[Once joint_transition_cases] >> rpt strip_tac >>
  drule_all forwarding_active_lookup >> strip_tac >>
  drule_all forwarding_suffix_opcode >> strip_tac >>
  gvs[is_terminator_def] >>
  (Cases_on `i0.inst_opcode = REVERT`
   >- metis_tac[forwarding_revert_no_step]) >>
  gvs[] >>
  TRY (qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
       simp[step_inst_non_invoke] >> strip_tac >>
       drule step_inst_base_intret_opcodes >> simp[] >> NO_TAC) >>
  `s'.vs_current_bb = v.vs_current_bb` by
    (irule forwarding_step_control >> metis_tac[]) >>
  simp[joint_revert_suffix_def] >>
  gvs[revert_forward_pair_def] >> decide_tac
QED

Theorem joint_trace_revert_suffix:
  !j k. joint_trace vs0 C q0 es qs q /\ k <= j /\ j <= LENGTH es /\
  ALL_DISTINCT (fn_labels fn) /\
  joint_revert_suffix fn bb i r (EL k (q0::qs)) ==>
  joint_revert_suffix fn bb i r (EL j (q0::qs))
Proof
  Induct >> rpt strip_tac >- gvs[] >>
  Cases_on `k = SUC j` >- gvs[] >>
  `k <= j /\ j < LENGTH es` by decide_tac >>
  `joint_revert_suffix fn bb i r (EL j (q0::qs))` by
    (first_x_assum irule >> simp[] >> qexists_tac `k` >> simp[]) >>
  drule joint_trace_edge_at >> disch_then (qspec_then `j` mp_tac) >>
  simp[] >> strip_tac >> irule joint_revert_suffix_step >> simp[] >>
  goal_assum (drule_at (Pat `joint_transition _ _ _ _`)) >> simp[]
QED

Theorem joint_revert_suffix_read:
  ALL_DISTINCT (fn_labels fn) /\ joint_revert_suffix fn bb i r q /\
  q = JointConfig stk PG G tn current inst s oms om hs h /\
  active_inst current inst s /\ byte IN joint_reads q ==>
  in_revert_forward current s
Proof
  strip_tac >> gvs[joint_revert_suffix_def] >>
  drule_all forwarding_active_lookup >> strip_tac >>
  drule_all forwarding_suffix_opcode >> strip_tac >>
  gvs[joint_reads_def, source_memory_read_ranges_def, range_bytes_def] >>
  simp[in_revert_forward_def, revert_forward_at_def] >> metis_tac[]
QED

Theorem joint_reachable_forwarding_control[local]:
  joint_config_reachable vs0 C (JointConfig stk PG G tn fn inst s oms om hs h) /\
  o1_ctx_shape C ==>
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s
Proof
  simp[joint_config_reachable_def] >> strip_tac >>
  drule joint_origin_history_projection >> strip_tac >>
  drule frame_history_cfg_invariant >>
  gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> strip_tac >>
  `wf_function fn` by metis_tac[] >>
  conj_tac >- gvs[wf_function_def] >>
  qpat_x_assum `joint_origin_history _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[Once joint_origin_history_cases] >> rpt strip_tac >> simp[]
QED

Theorem joint_trace_nonrevert_read:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ k <= j /\ j <= LENGTH es /\
  EL k (q0::qs) = JointConfig stk0 PG0 G0 tn0 fn0 inst0 s0 oms0 om0 hs0 h0 /\
  EL j (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  byte IN joint_reads (EL j (q0::qs)) /\ ~in_revert_forward fn s ==>
  ~in_revert_forward fn0 s0
Proof
  strip_tac >>
  `LENGTH es = LENGTH qs` by metis_tac[joint_chain_length, joint_trace_def] >>
  `joint_config_reachable vs0 C (EL k (q0::qs)) /\
   joint_config_reachable vs0 C (EL j (q0::qs))` by
    (drule joint_trace_prefix_reachable >>
     pure_rewrite_tac[EVERY_EL] >> strip_tac >>
     conj_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  `ALL_DISTINCT (fn_labels fn0) /\ active_inst fn inst s` by
    metis_tac[joint_reachable_forwarding_control] >>
  spose_not_then mp_tac >>
  rewrite_tac[in_revert_forward_def, revert_forward_at_def] >>
  disch_then (qx_choose_then `bb` strip_assume_tac) >>
  `joint_revert_suffix fn0 bb s0.vs_inst_idx j' (EL k (q0::qs)) \/
   joint_revert_suffix fn0 bb j' s0.vs_inst_idx (EL k (q0::qs))` by
    (simp[joint_revert_suffix_def] >>
     gvs[revert_forward_pair_def] >> metis_tac[]) >>
  `joint_revert_suffix fn0 bb s0.vs_inst_idx j' (EL j (q0::qs)) \/
   joint_revert_suffix fn0 bb j' s0.vs_inst_idx (EL j (q0::qs))` by
    metis_tac[joint_trace_revert_suffix] >>
  metis_tac[joint_revert_suffix_read]
QED

Definition joint_nonrevert_def:
  joint_nonrevert (JointConfig stk PG G tn fn inst s oms om hs h) <=>
    ~in_revert_forward fn s
End

Theorem joint_trace_nonrevert_read_at:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ k <= j /\ j <= LENGTH es /\
  byte IN joint_reads (EL j (q0::qs)) /\ joint_nonrevert (EL j (q0::qs)) ==>
  joint_nonrevert (EL k (q0::qs))
Proof
  Cases_on `EL k (q0::qs)` >> Cases_on `EL j (q0::qs)` >>
  simp[joint_nonrevert_def] >> metis_tac[joint_trace_nonrevert_read]
QED

Theorem joint_trace_nonrevert_interval:
  joint_trace vs0 C q0 es qs q /\ o1_ctx_shape C /\ n <= j /\ j <= LENGTH es /\
  byte IN joint_reads (EL j (q0::qs)) /\ joint_nonrevert (EL j (q0::qs)) ==>
  !k. n <= k /\ k <= j ==> joint_nonrevert (EL k (q0::qs))
Proof
  metis_tac[joint_trace_nonrevert_read_at]
QED
