Theory concretizePtrDallocaPersistentChannels
Ancestors
  passSharedDefs concretizeMemLocDefs concretizePtrDallocaPersistentSteps concretizePtrStorageWriteFamily
  concretizePtrCallFamily concretizePtrRequestCompletionProbe
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrTaggedSupport
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizePtrAllocationSize
  concretizePtrOpaqueRetpc concretizePtrValueTransport concretizePtrRequestHistory
  concretizePtrTaintContent concretizePtrSharedFields concretizeStepStructure
  ptrDiscipline pointerConfinedDefs memLocDefs venomInst venomState venomWf
  venomExecSemantics venomCallOracleDefs extCallOracle
  o1PassContract unitShapeDefs unitLabelMapIdentity codegenRel contextCodegenRel
  list finite_map pred_set

(* Precompile selection depends on the scalar address and value, not on
   relocated input bytes.  Thus adoption does not require a copy-read IH. *)
Theorem ptr_dalloca_completion_adoption:
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_outcomes = t.vs_outcomes /\
  consume_call_outcome (venom_call_request s addr value ao az st) ro rz s = (w,u) /\
  consume_call_outcome (venom_call_request t addr value at azt stt) rt rzt t = (v,z) ==>
  (ptr_call_adopted s u = ptr_call_adopted t z)
Proof
  strip_tac >> drule ptr_call_completion_adopted >>
  rev_drule ptr_call_completion_adopted >>
  simp[computed_precompile_addresses, venom_call_request_def]
QED

Theorem ptr_dalloca_ext_call_adoption[local]:
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_outcomes = t.vs_outcomes /\
  exec_ext_call inst s gas addr value ao az ro rz st = OK post /\
  exec_ext_call inst t gast addr value at azt rt rzt stt = OK postT ==>
  (ptr_call_adopted s post = ptr_call_adopted t postT)
Proof
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq", AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `consume_call_outcome (venom_call_request s addr value ao az st)
    (w2n ro) (w2n rz) s` >>
  Cases_on `consume_call_outcome (venom_call_request t addr value at azt stt)
    (w2n rt) (w2n rzt) t` >>
  gvs[Excl "consume_call_outcome_eq", AllCaseEqs()] >>
  drule_all ptr_dalloca_completion_adoption >>
  simp[ptr_call_adopted_def, update_var_def]
QED


Theorem ptr_dalloca_store_selector_clean[local]:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_operands = [key;data] /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [SSTORE;TSTORE;ISTORE] ==>
  ptr_nonopaque_operand fn key /\ op_prov TG key = NONE /\ op_taint tn key = {}
Proof
  strip_tac >>
  `EVERY (ptr_nonopaque_operand fn) inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts fn) ==> _`
       (qspec_then `inst` mp_tac) >> fs[MEM] >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
          mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  `op_prov TG key = NONE` by
    (Cases_on `key` >> simp[op_prov_def] >>
     rename1 `FLOOKUP TG u = NONE` >>
     Cases_on `FLOOKUP TG u` >> simp[] >> gvs[] >> metis_tac[]) >>
  simp[] >> reverse conj_tac
  >- (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> fs[MEM] >>
      simp[taint_ok_def] >> metis_tac[]) >>
  gvs[]
QED

Theorem ptr_dalloca_store_selector_equal:
  fn_ptr_ok P fn /\ opaque_use_ok fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\ inst.inst_operands = [key;data] /\
  (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P fn) /\
  MEM inst.inst_opcode [SSTORE;TSTORE;ISTORE] /\
  ptr_mixed_vars births positions (TG:(string,num # num) fmap) tn fn ft s t /\
  s.vs_labels = t.vs_labels ==>
  eval_operand key t = eval_operand key s
Proof
  strip_tac >>
  drule_all ptr_dalloca_store_selector_clean >> strip_tac >>
  drule_all ptr_mixed_vars_eval >>
  simp[] >>
  Cases_on `eval_operand key s` >> Cases_on `eval_operand key t` >>
  simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]
QED

Theorem ptr_dalloca_persistent_context[local]:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs ==>
  ?P. fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn /\
    MEM a.po_inst (fn_insts a.po_fn) /\ inst_wf a.po_inst /\
    taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
    (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn) /\
    ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
      a.po_state at.po_state /\
    ptr_history_content a.po_taint a.po_state at.po_state /\
    a.po_state.vs_labels = at.po_state.vs_labels
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by
    (drule concretizePtrOperationalOpcodesTheory.ptr_frame_context_membership >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
        EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  qexists `P` >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  fs[ptr_paired_sample_def, ptr_discipline_def, o1_ctx_shape_def,
     o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >>
  metis_tac[ptr_history_content_labels]
QED

Theorem ptr_dalloca_paired_persistent_selectors:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs ==>
  !key data. MEM a.po_inst.inst_opcode [SSTORE;TSTORE;ISTORE] /\
    a.po_inst.inst_operands = [key;data] ==>
    eval_operand key at.po_state = eval_operand key a.po_state
Proof
  strip_tac >> drule_all ptr_dalloca_persistent_context >> strip_tac >>
  rpt strip_tac >> drule_all ptr_dalloca_store_selector_equal >> simp[]
QED

Theorem ptr_dalloca_paired_call_adoption:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  a.po_inst.inst_opcode = CALL /\
  step_inst fuel C a.po_inst a.po_state = OK post /\
  step_inst fuelT C' a.po_inst at.po_state = OK postT ==>
  (ptr_call_adopted a.po_state post = ptr_call_adopted at.po_state postT)
Proof
  strip_tac >> drule_all ptr_dalloca_persistent_context >> strip_tac >>
  `?gasop addrop valop ao az ro rz.
    a.po_inst.inst_operands = [gasop;addrop;valop;ao;az;ro;rz]` by
    (qpat_x_assum `inst_wf _` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `eval_operands [gasop;addrop;valop;az;rz] a.po_state =
   eval_operands [gasop;addrop;valop;az;rz] at.po_state` by
    (drule_all (SRULE [] (Q.INST [`pre` |-> `[gasop;addrop;valop]`,
       `gas` |-> `gasop`, `addr` |-> `addrop`, `value` |-> `valop`]
       ptr_call_operand_transport)) >> simp[]) >>
  suspend "evaluate"
QED
Resume ptr_dalloca_paired_call_adoption[evaluate]:
  qpat_x_assum `step_inst fuel C _ _ = OK post` mp_tac >>
  qpat_x_assum `step_inst fuelT C' _ _ = OK postT` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, Once opcode_case_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `eval_operands _ _ = _` mp_tac >>
  simp[eval_operands_def] >> strip_tac >> gvs[] >>
  `a.po_state.vs_call_ctx = at.po_state.vs_call_ctx /\
   a.po_state.vs_outcomes = at.po_state.vs_outcomes` by
    (fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
        ptr_core_shared_def, ptr_shared_fields_def]) >>
  drule_all ptr_dalloca_ext_call_adoption >> simp[]
QED
Finalise ptr_dalloca_paired_call_adoption

(* Actual executions, rather than independent guessed poststates, determine
   the reset guard.  Incoming variable-mask inclusion supplies only store
   data inclusion; selector equality above comes from clean scalar values. *)
Theorem ptr_dalloca_actual_persistent_next:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ ptr_discipline lo C vs /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  step_inst fuel C a.po_inst a.po_state = OK post /\
  step_inst fuelT C' at.po_inst at.po_state = OK postT /\
  at.po_taint.t_stor SUBSET a.po_taint.t_stor /\
  at.po_taint.t_trans SUBSET a.po_taint.t_trans /\
  at.po_taint.t_imm SUBSET a.po_taint.t_imm /\
  (!op. MEM op a.po_inst.inst_operands ==>
    op_taint at.po_taint op SUBSET op_taint a.po_taint op) ==>
  (step_taint at.po_inst at.po_state postT at.po_taint).t_stor SUBSET
    (step_taint a.po_inst a.po_state post a.po_taint).t_stor /\
  (step_taint at.po_inst at.po_state postT at.po_taint).t_trans SUBSET
    (step_taint a.po_inst a.po_state post a.po_taint).t_trans /\
  (step_taint at.po_inst at.po_state postT at.po_taint).t_imm SUBSET
    (step_taint a.po_inst a.po_state post a.po_taint).t_imm
Proof
  strip_tac >>
  `!key data. MEM a.po_inst.inst_opcode [SSTORE;TSTORE;ISTORE] /\
    a.po_inst.inst_operands = [key;data] ==>
    eval_operand key at.po_state = eval_operand key a.po_state` by
    ((metisTools.METIS_TAC [DB.fetch "concretizePtrDallocaPersistentChannels" "ptr_dalloca_paired_persistent_selectors"])) >>
  Cases_on `a.po_inst.inst_opcode = ALLOCA`
  >- suspend "alloca" >>
  `at.po_inst = a.po_inst` by
    gvs[concretize_inst_with_positions_def] >>
  `a.po_inst.inst_opcode = CALL ==>
    ptr_call_adopted a.po_state post = ptr_call_adopted at.po_state postT` by
    (strip_tac >> metis_tac[ptr_dalloca_paired_call_adoption]) >>
  irule ptr_dalloca_persistent_next >> simp[] >>
  gvs[ptr_call_adopted_def]
QED
Resume ptr_dalloca_actual_persistent_next[alloca]:
  `at.po_inst = a.po_inst \/ at.po_inst.inst_opcode = ASSIGN \/
    at.po_inst.inst_opcode = NOP` by
    (gvs[concretize_inst_with_positions_def, AllCaseEqs(),
       mk_assign_inst_def, mk_nop_inst_def] >>
     qpat_x_assum `_ = at.po_inst` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  gvs[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def]
QED
Finalise ptr_dalloca_actual_persistent_next
