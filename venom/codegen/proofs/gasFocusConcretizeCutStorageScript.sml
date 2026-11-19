Theory gasFocusConcretizeCutStorage
Ancestors
  concretizePtrOrdinaryNext concretizePtrRequestHistory
  concretizePtrOpaqueRetpc concretizePtrValueTransport
  concretizePtrTaintStorageProbe concretizePtrTaintContent
  concretizePtrRequestCompletionProbe
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrLedgerProbe concretizePtrChronologicalHistory
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrOperationalOpcodes concretizePtrSourceOwnership
  ghostPcTransportPtr opcodeClass venomInst venomState venomExecSemantics
  venomInstProofs1 venomMemProps concretizeStepStructure
  ptrDiscipline pointerConfinedDefs memLocDefs codegenRel contextCodegenRel venomWf
  unitShapeDefs unitLabelMapIdentity o1PassContract frameViewFacts
  list finite_map pred_set

Theorem focus_storage_scalar[local]:
  ptr_use_ok P pv i /\ FDOM TG SUBSET pv /\ MEM op i.inst_operands /\
  MEM i.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE] ==>
  op_prov TG op = NONE
Proof
  Cases_on `op` >> simp[op_prov_def] >> strip_tac >>
  rename1 `FLOOKUP TG v = NONE` >>
  `v NOTIN pv` by
    (qpat_x_assum `ptr_use_ok _ _ _` mp_tac >>
     fs[MEM] >> simp[ptr_use_ok_def, is_pointer_preserving_op_def,
                     mem_read_ops_def, mem_write_ops_def] >> metis_tac[]) >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem focus_storage_key[local]:
  taint_ok f tn i s /\
  ((MEM i.inst_opcode [SLOAD; TLOAD] /\ i.inst_operands = [key]) \/
   (MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_operands = [key; data])) ==>
  op_taint tn key = {}
Proof
  strip_tac >> gvs[MEM, taint_ok_def] >> metis_tac[]
QED

Theorem focus_storage_operand[local]:
  ptr_mixed_vars births positions (TG : (string,num # num) fmap) tn f g s t /\
  ptr_history_content tn s t /\ EVERY (ptr_nonopaque_operand f) i.inst_operands /\
  ptr_use_ok P pv i /\ FDOM TG SUBSET pv /\ MEM op i.inst_operands /\
  MEM i.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE] ==>
  ptr_lookup_transport births positions NONE (op_taint tn op)
    (eval_operand op s) (eval_operand op t)
Proof
  strip_tac >>
  `op_prov TG op = NONE` by (drule_all focus_storage_scalar >> simp[]) >>
  `ptr_nonopaque_operand f op` by fs[EVERY_MEM] >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  drule_all ptr_mixed_vars_eval >> simp[]
QED

Theorem focus_storage_read[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  ptr_lookup_transport births positions NONE {} (eval_operand key s) (eval_operand key t) /\
  MEM i.inst_opcode [SLOAD; TLOAD] /\ i.inst_operands = [key] /\
  i.inst_outputs = [out] /\ ~retpc_var f out /\ step_inst_base i t = OK postt ==>
  ?post. step_inst_base i s = OK post /\
    ptr_mixed_vars births positions (step_prov PT TG i post)
      (step_taint i s post tn) f g post postt /\
    ptr_history_content (step_taint i s post tn) post postt
Proof
  strip_tac >>
  `?k. eval_operand key t = SOME k` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     fs[MEM] >> simp[step_inst_base_opcode_eqs, exec_read1_def, AllCaseEqs()] >> metis_tac[]) >>
  `eval_operand key s = SOME k` by
    fs[ptr_lookup_transport_some_right, ptr_value_transport_scalar_empty] >>
  `ptr_taint_content tn (s with vs_requests := t.vs_requests) t` by
    metis_tac[ptr_history_content_current] >>
  `?u v. step_inst_base i s = OK (update_var out u s) /\
      postt = update_var out v t /\ word_agree_except (out_taint tn i s) u v` by
    (fs[MEM] >> gvs[step_inst_base_opcode_eqs, exec_read1_def] >>
     qexistsl [`if i.inst_opcode = SLOAD then sload k s else tload k s`,
               `if i.inst_opcode = SLOAD then sload k t else tload k t`] >>
     simp[out_taint_def] >>
     drule ptr_taint_content_sload >> drule ptr_taint_content_tload >>
     simp[sload_def, tload_def, contract_storage_def, contract_transient_def]) >>
  qexists `update_var out u s` >> simp[] >> gvs[] >>
  (conj_tac
  >- (drule ptr_mixed_vars_update >> disch_then irule >> simp[] >>
      fs[MEM] >> simp[step_prov_def, out_prov_def, set_prov_def,
        step_taint_def, set_var_taint_def, op_taint_def, ptr_value_transport_def,
        FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
      rpt strip_tac >> fs[ptr_mixed_vars_def, op_taint_def, FLOOKUP_UPDATE]) >>
  drule_at (Pat `ptr_history_content _ _ _`) ptr_history_content_masks >>
  disch_then (qspec_then `step_taint i s (update_var out u s) tn` mp_tac) >>
  fs[MEM] >> simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def])
QED

Theorem focus_storage_write[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  ptr_lookup_transport births positions NONE {} (eval_operand key s) (eval_operand key t) /\
  ptr_lookup_transport births positions NONE (op_taint tn data)
    (eval_operand data s) (eval_operand data t) /\
  MEM i.inst_opcode [SSTORE; TSTORE] /\ i.inst_operands = [key; data] /\
  i.inst_outputs = [] /\ step_inst_base i t = OK postt ==>
  ?post. step_inst_base i s = OK post /\
    ptr_mixed_vars births positions (step_prov PT TG i post)
      (step_taint i s post tn) f g post postt /\
    ptr_history_content (step_taint i s post tn) post postt
Proof
  strip_tac >>
  `?k v. eval_operand key t = SOME k /\ eval_operand data t = SOME v /\
     ~t.vs_call_ctx.cc_static` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     fs[MEM] >> Cases_on `eval_operand key t` >> Cases_on `eval_operand data t` >>
     simp[step_inst_base_opcode_eqs, exec_write2_def, eval_operands_def, AllCaseEqs()]) >>
  `eval_operand key s = SOME k` by
    fs[ptr_lookup_transport_some_right, ptr_value_transport_scalar_empty] >>
  `?u. eval_operand data s = SOME u /\ word_agree_except (op_taint tn data) u v` by
    fs[ptr_lookup_transport_some_right, ptr_value_transport_def] >>
  `s.vs_call_ctx = t.vs_call_ctx` by metis_tac[ptr_history_content_call_ctx] >>
  fs[MEM] >> gvs[step_inst_base_opcode_eqs, exec_write2_def, eval_operands_def] >>
  simp[step_prov_def, out_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  (conj_tac
   >- (irule ptr_mixed_vars_fields >> goal_assum (drule_at Any) >>
       simp[step_taint_def, set_var_taint_def, DRESTRICT_UNIV, sstore_def, tstore_def]))
  >- (irule ptr_history_content_masks >>
      drule_all ptr_history_sstore >> disch_then (qspec_then `k` assume_tac) >>
      goal_assum (drule_at Any) >>
      simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def]) >>
  irule ptr_history_content_masks >>
  qexists `tn with t_trans := key_update tn.t_trans k (op_taint tn data)` >>
  simp[step_taint_def, store_taint_def, adopt_reset_def, imm_taint_def] >>
  qpat_x_assum `ptr_history_content _ _ _` mp_tac >>
  simp[ptr_history_content_def] >> strip_tac >>
  drule_all ptr_taint_content_tstore >>
  disch_then (qspec_then `k` mp_tac) >> simp[tstore_def]
QED

Theorem focus_storage_reflect[local]:
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  EVERY (ptr_nonopaque_operand f) i.inst_operands /\
  ptr_use_ok P pv i /\ FDOM TG SUBSET pv /\ taint_ok f tn i s /\
  MEM i.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE] /\
  inst_wf i /\ ssa_form f /\ MEM i (fn_insts f) /\ step_inst_base i t = OK postt ==>
  ?post. step_inst_base i s = OK post /\
    ptr_mixed_vars births positions (step_prov PT TG i post)
      (step_taint i s post tn) f g post postt /\
    ptr_history_content (step_taint i s post tn) post postt
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==>
      ptr_lookup_transport births positions NONE (op_taint tn op)
        (eval_operand op s) (eval_operand op t)` by
    (rpt strip_tac >> drule_all focus_storage_operand >> simp[]) >>
  Cases_on `MEM i.inst_opcode [SLOAD; TLOAD]`
  >- (`?key out. i.inst_operands = [key] /\ i.inst_outputs = [out]` by
        (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
      `~retpc_var f out` by
        (irule noncopy_output_not_retpc >> conj_tac >- simp[] >>
         qexists `i` >> fs[MEM]) >>
      `op_taint tn key = {}` by (irule focus_storage_key >> metis_tac[]) >>
      `ptr_lookup_transport births positions NONE {} (eval_operand key s) (eval_operand key t)` by
        gvs[] >>
      drule_all focus_storage_read >> simp[]) >>
  `MEM i.inst_opcode [SSTORE; TSTORE]` by fs[MEM] >>
  `?key data. i.inst_operands = [key;data] /\ i.inst_outputs = []` by
    (fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `op_taint tn key = {}` by (irule focus_storage_key >> metis_tac[]) >>
  `ptr_lookup_transport births positions NONE {} (eval_operand key s) (eval_operand key t) /\
   ptr_lookup_transport births positions NONE (op_taint tn data)
     (eval_operand data s) (eval_operand data t)` by
    (gvs[] >> qpat_assum `!op. _ \/ _ ==> ptr_lookup_transport _ _ _ _ _ _` mp_tac >>
     metis_tac[]) >>
  drule_all focus_storage_write >> simp[]
QED

Theorem focus_storage_observed[local]:
  MEM a.po_inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE] /\ ptr_chrono_step C a b ==>
  ?post. step_inst_base a.po_inst a.po_state = OK post /\
    b.po_state = post with vs_inst_idx := SUC a.po_state.vs_inst_idx /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
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
  (`step_inst_base a.po_inst a.po_state = OK s'` by gvs[step_inst_non_invoke]) >>
  (`~is_terminator a.po_inst.inst_opcode` by simp[is_terminator_def]) >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem ptr_focus_storage_step:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  EVERY ssa_form C.ctx_functions /\
  ptr_use_ok P pv a.po_inst /\ FDOM TG SUBSET pv /\
  taint_ok a.po_fn a.po_taint a.po_inst a.po_state /\
  MEM a.po_inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE] /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z TG'. TG' = step_prov PT TG a.po_inst z.po_state /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG' saved entries
      (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
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
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> simp[] >> fs[MEM]) >>
  `at.po_inst = a.po_inst /\ ~is_terminator a.po_inst.inst_opcode /\
    a.po_inst.inst_opcode <> INVOKE /\ a.po_inst.inst_opcode <> NOP /\
    a.po_inst.inst_opcode <> ALLOCA` by
    (fs[MEM] >> simp[concretize_positions_unchanged, is_terminator_def]) >>
  `MEM at.po_inst.inst_opcode [SLOAD; TLOAD; SSTORE; TSTORE]` by asm_rewrite_tac[] >>
  drule_all focus_storage_observed >>
  disch_then (qx_choose_then `postt` strip_assume_tac) >>
  `step_inst_base a.po_inst at.po_state = OK postt` by
    (qpat_assum `at.po_inst = a.po_inst` (once_rewrite_tac o single o SYM) >> asm_rewrite_tac[]) >>
  qpat_assum `ptr_paired_sample _ _ _ _`
    (strip_assume_tac o SRULE [ptr_paired_sample_def]) >>
  drule_all focus_storage_reflect >>
  disch_then (qspec_then `PT` (qx_choose_then `post` strip_assume_tac)) >>
  suspend "attach"
QED

Resume ptr_focus_storage_step[attach]:
  `step_inst 0 C a.po_inst a.po_state = OK post` by simp[step_inst_non_invoke] >>
  `post.vs_current_bb = a.po_state.vs_current_bb /\
   post.vs_prev_bb = a.po_state.vs_prev_bb /\ post.vs_params = a.po_state.vs_params` by
    (qpat_assum `step_inst_base a.po_inst a.po_state = OK post`
       (mp_then Any mp_tac step_inst_base_preserves_all) >> simp[]) >>
  `post.vs_allocas = a.po_state.vs_allocas` by
    (irule step_inst_base_preserves_allocas >> qexists `a.po_inst` >> simp[]) >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    (irule ptr_ordinary_next_active >> simp[] >>
     conj_tac >- fs[wf_function_def, EVERY_MEM] >> qexists `a.po_inst` >> simp[]) >>
  `ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn)` by
    (conj_asm1_tac >- fs[wf_function_def] >>
     fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  drule ptr_paired_stage_local_allocas >>
  disch_then (qspecl_then [`o1_walk_view rpolicy 2`,`rpolicy`] mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  qabbrev_tac `TG' = step_prov PT TG a.po_inst z.po_state` >>
  `ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries)` by
    (simp[ptr_paired_sample_def, Abbr `TG'`, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
     qpat_assum `zt.po_state = _` (once_rewrite_tac o single) >>
     simp[] >> irule ptr_mixed_vars_fields >> goal_assum (drule_at Any) >> simp[]) >>
  `ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries)` by
    fs[ptr_paired_params_def, Abbr `z`, ptr_ledger_next_def, ptr_observe_def] >>
  qexists `z` >> gs[Abbr `TG'`] >>
  drule ptr_paired_prefix_ordinary_nonwrite >> disch_then irule >>
  simp[Abbr `z`, ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def] >>
  fs[MEM] >> simp[step_writes_def, range_bytes_def, source_memory_write_ranges_def] >>
  qexistsl [`0`,`post`] >> simp[]
QED
Finalise ptr_focus_storage_step
