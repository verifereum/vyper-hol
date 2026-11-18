Theory gasFocusConcretizeCutCreation
Ancestors
  concretizePtrOrdinaryNext concretizePtrRequestHistory
  concretizePtrOpaqueRetpc concretizePtrSharedFields concretizePtrValueTransport
  lowerDloadPtrCreate lowerDloadSafetyCreate o1LowerDloadRangeTransport
  concretizePtrTaintContent concretizePtrPairedPrefix
  venomCallOracleDefs venomInstProofs venomState ptrDiscipline memoryReadRel
  venomExecSemantics codegenRel contextCodegenRel memLocDefs
  concretizePtrPairedFields concretizeStepStructure opcodeClass
  concretizePtrLedgerProbe concretizePtrChronologicalHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrOperationalOpcodes concretizePtrSourceOwnership
  venomInst venomWf unitLabelMapIdentity unitShapeDefs o1PassContract
  frameViewFacts list finite_map pred_set

(* The pointer argument is transported; the scalar arguments are unchanged. *)
Theorem focus_create_operand_transport[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ s.vs_labels = t.vs_labels /\
  EVERY (ptr_nonopaque_operand f) i.inst_operands /\
  ptr_use_ok P pv i /\ FDOM TG SUBSET pv /\ taint_ok f tn i s /\
  ((i.inst_opcode = CREATE /\ i.inst_operands = [vop;off;sz] /\ args = [vop;sz]) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [vop;off;sz;salt] /\ args = [vop;sz;salt])) ==>
  (!op. MEM op args ==> eval_operand op s = eval_operand op t) /\
  ptr_lookup_transport births positions (op_prov TG off) {}
    (eval_operand off s) (eval_operand off t) /\
  tn.t_stor = {} /\ tn.t_trans = {}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!op. MEM op args ==> op_prov TG op = NONE /\
     (!arg. MEM arg i.inst_operands ==> op_taint tn arg = {}) /\
     tn.t_stor = {} /\ tn.t_trans = {}` by
    (gen_tac >> disch_tac >>
     `((i.inst_opcode = CREATE /\ i.inst_operands = [vop;off;sz] /\
        MEM op [vop;sz]) \/
       (i.inst_opcode = CREATE2 /\ i.inst_operands = [vop;off;sz;salt] /\
        MEM op [vop;sz;salt]))` by metis_tac[] >>
     metis_tac[dload_create_operand_safety]) >>
  `(!arg. MEM arg i.inst_operands ==> op_taint tn arg = {}) /\
   tn.t_stor = {} /\ tn.t_trans = {}` by
    (qpat_assum `!op. MEM op args ==> _` (qspec_then `vop` mp_tac) >> gvs[]) >>
  `!op. MEM op i.inst_operands ==>
    ptr_lookup_transport births positions (op_prov TG op) {}
      (eval_operand op s) (eval_operand op t)` by
    (rpt strip_tac >>
     `ptr_nonopaque_operand f op` by fs[EVERY_MEM] >>
     drule_all ptr_mixed_vars_eval >> simp[]) >>
  `!op. MEM op args ==> MEM op i.inst_operands` by (gvs[] >> metis_tac[]) >>
  `MEM off i.inst_operands` by gvs[] >>
  simp[] >> rpt strip_tac >>
  `ptr_lookup_transport births positions NONE {}
    (eval_operand op s) (eval_operand op t)` by metis_tac[] >>
  Cases_on `eval_operand op s` >> Cases_on `eval_operand op t` >>
  gvs[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]
QED

Theorem focus_create_stores[local]:
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} ==>
  s.vs_accounts = t.vs_accounts /\ s.vs_transient = t.vs_transient
Proof
  strip_tac >> drule ptr_history_content_call_ctx >> strip_tac >>
  `contract_storage s = contract_storage t /\
   contract_transient s = contract_transient t` by
    (fs[ptr_history_content_def, ptr_taint_content_def] >>
     fs[storage_agree_except_def, key_taint_def, contract_storage_def,
        contract_transient_def, word_agree_except_bits,
        FUN_EQ_THM, fcpTheory.CART_EQ]) >>
  fs[ptr_history_content_def, ptr_taint_content_def,
     contract_storage_def, contract_transient_def,
     vfmStateTheory.lookup_account_def] >>
  conj_tac
  >- (simp[FUN_EQ_THM] >> qx_gen_tac `addr` >>
      `(s.vs_accounts addr).storage = (t.vs_accounts addr).storage` by
        (Cases_on `addr = s.vs_call_ctx.cc_address` >> gvs[]) >>
      qpat_x_assum `!a. _ with storage := _ = _`
        (qspec_then `addr` mp_tac) >>
      simp[vfmStateTheory.account_state_component_equality]) >>
  simp[FUN_EQ_THM] >> metis_tac[]
QED

Theorem focus_create_execute[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  ptr_history_content tn s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n off) (w2n sz) s = read_memory (w2n off') (w2n sz) t /\
  MEM i.inst_opcode [CREATE; CREATE2] /\
  i.inst_outputs = [out] /\ ~retpc_var f out /\
  exec_create i t value off' sz salt = OK z ==>
  ?u. exec_create i s value off sz salt = OK u /\
    ptr_history_content tn u z /\
    ptr_mixed_vars births positions (step_prov PT TG i u)
      (step_taint i s u tn) f g u z
Proof
  strip_tac >> drule_all focus_create_stores >> strip_tac >>
  `venom_create_request s value off sz salt = venom_create_request t value off' sz salt`
    by (irule venom_create_request_eq_from_slice >> simp[]) >>
  `s.vs_outcomes = t.vs_outcomes` by
    fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def] >>
  drule_all ld_create_exec_steps >> strip_tac >>
  gvs[Excl "consume_create_outcome_eq"] >>
  (conj_tac
  >- (qmatch_asmsub_abbrev_tac `consume_create_outcome rq s` >>
      `ptr_request_history (record_request rq s.vs_requests)
         (record_request rq t.vs_requests)` by
        (irule ptr_request_record >> fs[ptr_history_content_def]) >>
      fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
         ptr_core_shared_def, ptr_shared_fields_def] >>
      gvs[consume_create_outcome_eq] >>
      simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
           ptr_core_shared_def, ptr_shared_fields_def,
           contract_storage_def, contract_transient_def,
           storage_agree_except_def, word_agree_except_def])) >>
  `ptr_mixed_vars births positions TG tn f g rs rt` by
    (irule ptr_mixed_vars_fields >>
     rpt (goal_assum (drule_at Any)) >>
     qpat_x_assum `consume_create_outcome _ s = _` mp_tac >>
     qpat_x_assum `consume_create_outcome _ t = _` mp_tac >>
     simp[consume_create_outcome_eq] >> rpt strip_tac >> gvs[]) >>
  drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
  fs[MEM] >>
  simp[step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, set_var_taint_def, out_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def, ptr_value_transport_def] >>
  rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def, word_agree_except_def]
QED

(* The read premise refers only to the range evaluated by this instruction. *)
Theorem focus_create_reflect[local]:
  ptr_mixed_vars births positions TG tn f g s t /\
  ptr_history_content tn s t /\
  EVERY (ptr_nonopaque_operand f) i.inst_operands /\
  ptr_use_ok P pv i /\ FDOM TG SUBSET pv /\ taint_ok f tn i s /\
  MEM i.inst_opcode [CREATE; CREATE2] /\
  i.inst_outputs = [out] /\ ~retpc_var f out /\ ~in_revert_forward f s /\
  (!ops x y sz j. mem_read_ops i = SOME ops /\
    eval_operand ops.iao_ofst s = SOME x /\ eval_operand ops.iao_ofst t = SOME y /\
    MEM (w2n x,sz) (source_memory_read_ranges i s) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) /\
    j < sz /\ w2n x + j NOTIN tn.t_mem ==>
    read_byte (w2n x + j) s.vs_memory = read_byte (w2n y + j) t.vs_memory) /\
  step_inst_base i t = OK postt ==>
  ?post. step_inst_base i s = OK post /\ ptr_history_content tn post postt /\
    ptr_mixed_vars births positions (step_prov PT TG i post)
      (step_taint i s post tn) f g post postt
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ld_create_dispatch >>
  disch_then (qx_choose_then `vop` (qx_choose_then `oop` (qx_choose_then `sop`
    (qx_choose_then `sa` (qx_choose_then `v` (qx_choose_then `y`
      (qx_choose_then `sz` (qx_choose_then `salt` (map_every assume_tac o CONJUNCTS))))))))) >>
  `s.vs_labels = t.vs_labels /\ s.vs_call_ctx = t.vs_call_ctx` by
    metis_tac[ptr_history_content_labels, ptr_history_content_call_ctx] >>
  `?args. (i.inst_opcode = CREATE /\ i.inst_operands = [vop;oop;sop] /\ args = [vop;sop]) \/
    (i.inst_opcode = CREATE2 /\ i.inst_operands = [vop;oop;sop;sa] /\ args = [vop;sop;sa])`
    suffices_by (disch_then (qx_choose_then `args` assume_tac) >>
  drule_all focus_create_operand_transport >> strip_tac >>
  `?x. eval_operand oop s = SOME x /\
    ptr_lookup_transport births positions (op_prov TG oop) {} (SOME x) (SOME y)` by
    (Cases_on `eval_operand oop s` >> gvs[ptr_lookup_transport_def] >> metis_tac[]) >>
  `eval_operand vop s = SOME v /\ eval_operand sop s = SOME sz /\
   (i.inst_opcode = CREATE2 ==> eval_operand sa s = eval_operand sa t)` by
    (qpat_assum `_ \/ _` strip_assume_tac >> gvs[]) >>
  `MEM (w2n x,w2n sz) (source_memory_read_ranges i s)` by
    (qpat_assum `_ \/ _` strip_assume_tac >>
     gvs[source_memory_read_ranges_def, memory_range_of_operands_def,
         mem_read_ops_def, eval_operands_def]) >>
  `read_memory (w2n x) (w2n sz) s = read_memory (w2n y) (w2n sz) t` by
    (irule read_memory_eq_from_bytes >> rpt strip_tac >>
     `w2n x + q NOTIN tn.t_mem` by
       (irule taint_ok_observation_read >> simp[] >> metis_tac[MEM]) >>
     first_x_assum irule >> simp[] >>
     conj_tac >- (qexists `w2n sz` >> simp[]) >>
     qexists `<|iao_ofst := oop; iao_size := SOME sop; iao_max_size := SOME sop|>` >>
     qpat_assum `_ \/ _` strip_assume_tac >> gvs[mem_read_ops_def]) >>
  drule_all focus_create_execute >>
  disch_then (qspec_then `PT` (qx_choose_then `u` strip_assume_tac)) >>
  qexists `u` >> asm_rewrite_tac[] >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  gvs[step_inst_base_opcode_eqs, eval_operands_def]) >> metis_tac[]
QED

(* Invert the observed chronological edge; the internal return case is impossible. *)
Theorem focus_create_observed[local]:
  MEM a.po_inst.inst_opcode [CREATE; CREATE2] /\ ptr_chrono_step C a b ==>
  ?post. step_inst_base a.po_inst a.po_state = OK post /\
    b.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    active_inst b.po_fn b.po_inst b.po_state /\
    b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
    b.po_state.vs_prev_bb = a.po_state.vs_prev_bb /\
    b.po_state.vs_params = a.po_state.vs_params
Proof
  strip_tac >>
  qpat_x_assum `ptr_chrono_step _ _ _` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> gvs[is_terminator_def]
  >>~- ([`step_inst _ _ _ _ = IntRet _ _`],
    qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
    simp[step_inst_non_invoke] >> strip_tac >>
    drule step_inst_base_intret_opcodes >> simp[]) >>
  qpat_assum `step_inst _ _ _ _ = OK _`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[is_ext_call_op_def] >> strip_tac >>
  qexists `s'` >> gvs[step_inst_non_invoke]
QED

Theorem ptr_focus_creation_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  ptr_use_ok P pv a.po_inst /\ FDOM TG SUBSET pv /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  MEM a.po_inst.inst_opcode [CREATE; CREATE2] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ~in_revert_forward a.po_fn a.po_state /\ ptr_chrono_step C' at zt /\
  (!ops x y sz j. mem_read_ops a.po_inst = SOME ops /\
    eval_operand ops.iao_ofst a.po_state = SOME x /\
    eval_operand ops.iao_ofst at.po_state = SOME y /\
    MEM (w2n x,sz) (source_memory_read_ranges a.po_inst a.po_state) /\
    ptr_lookup_transport births positions (op_prov TG ops.iao_ofst) {} (SOME x) (SOME y) /\
    j < sz /\ w2n x + j NOTIN a.po_taint.t_mem ==>
    read_byte (w2n x + j) a.po_state.vs_memory = read_byte (w2n y + j) at.po_state.vs_memory) ==>
  ?z TG'. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `MEM a.po_fn C.ctx_functions /\ active_inst a.po_fn a.po_inst a.po_state` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def] >>
     strip_tac >> conj_tac >- (drule ptr_frame_context_membership >> simp[]) >>
     qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
  `wf_function a.po_fn /\ fn_inst_wf a.po_fn /\ opaque_use_ok a.po_fn /\ ssa_form a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `inst_wf a.po_inst` by (fs[fn_inst_wf_def, fn_insts_MEM, EVERY_MEM] >> metis_tac[]) >>
  `?out. a.po_inst.inst_outputs = [out] /\ ~retpc_var a.po_fn out` by
    (`?out. a.po_inst.inst_outputs = [out]` by (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
     qexists `out` >> simp[] >> irule noncopy_output_not_retpc >>
     conj_tac >- simp[] >>
     qexists `a.po_inst` >> fs[MEM]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `at.po_inst = a.po_inst /\ ~is_terminator a.po_inst.inst_opcode /\
    a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> NOP /\
    is_ext_call_op a.po_inst.inst_opcode` by
    (fs[MEM] >> simp[concretize_positions_unchanged, is_terminator_def, is_ext_call_op_def]) >>
  suspend "attach"
QED
Resume ptr_focus_creation_step[attach]:
  `MEM at.po_inst.inst_opcode [CREATE; CREATE2]` by asm_rewrite_tac[] >>
  qpat_assum `ptr_chrono_step C' at zt` (mp_then Any mp_tac focus_create_observed) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `postt` strip_assume_tac) >>
  `step_inst_base a.po_inst at.po_state = OK postt` by
    (qpat_assum `at.po_inst = a.po_inst` (once_rewrite_tac o single o SYM) >> asm_rewrite_tac[]) >>
  qpat_assum `ptr_paired_sample _ _ _ _`
    (strip_assume_tac o SRULE [ptr_paired_sample_def]) >>
  drule_all focus_create_reflect >>
  disch_then (qspec_then `PT` (qx_choose_then `post` strip_assume_tac)) >>
  `step_inst 0 C a.po_inst a.po_state = OK post` by simp[step_inst_non_invoke] >>
  qpat_assum `step_inst 0 C _ _ = OK post`
    (mp_then Any mp_tac venomInstProofsTheory.step_ext_call_preserves) >>
  simp[] >> strip_tac >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> simp[] >>
     conj_tac >- fs[wf_function_def, EVERY_MEM] >>
     qexists `a.po_inst` >> simp[]) >>
  `ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn)` by
    (conj_asm1_tac >- fs[wf_function_def] >>
     qpat_x_assum `ptr_paired_code _ _ _ _ _` mp_tac >>
     simp[ptr_paired_code_def] >> strip_tac >>
     simp[fn_labels_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qabbrev_tac `TG' = step_prov PT TG a.po_inst z.po_state` >>
  qexistsl [`z`,`TG'`] >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `TG'`, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     (reverse conj_tac >-
       (irule ptr_history_content_masks >> goal_assum (drule_at Any) >>
        fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def])) >>
     gvs[step_prov_def, out_prov_def] >>
     irule ptr_mixed_vars_fields >> rpt (goal_assum (drule_at Any)) >> simp[step_taint_def]) >>
  `ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries)` by
    (fs[ptr_paired_params_def, Abbr `TG'`, Abbr `z`, ptr_ledger_next_def, ptr_observe_def]) >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `TG'`, Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_prov_def, out_prov_def, step_writes_def,
     range_bytes_def, codegenRelTheory.source_memory_write_ranges_def] >>
  qexistsl [`0`,`post`] >> simp[]
QED
Finalise ptr_focus_creation_step
