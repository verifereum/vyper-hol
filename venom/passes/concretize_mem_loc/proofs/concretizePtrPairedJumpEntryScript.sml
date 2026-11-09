Theory concretizePtrPairedJumpEntry
Ancestors
  concretizePtrPairedEntry concretizePtrPairedPrefix concretizePtrPairedPrefixProbe
  concretizePtrPairedFields concretizePtrMixedPhi concretizePtrOpaqueRetpc
  concretizePtrSharedFields concretizePtrValueTransport concretizePtrPrefixLedger concretizePtrChronologicalHistory
  concretizePtrTaggedSupport concretizePtrParamSupport concretizePtrRequestHistory
  concretizePtrTaintContent
  concretizePtrDeletedGapHistory concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrActivationChronology frameCfgBoundary
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  venomExecSemantics venomState venomWf unitShapeDefs ptrDiscipline ptrDisciplineEmptyTaint
  pointerConfinedDefs memLocDefs
  unitLabelMapIdentity frameHistoryInstructions contextCodegenRel passSimulationDefs passSimulationProps venomExecProofs venomInst finite_map list

Theorem ptr_owned_jnz_scalar:
  ptr_source_ownership vs0 C h a tokens registry births PT TG saved /\
  ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  opaque_use_ok a.po_fn /\ MEM a.po_inst.inst_opcode [JNZ; DJMP] /\
  MEM cond a.po_inst.inst_operands ==>
  ptr_nonopaque_operand a.po_fn cond /\ op_prov TG cond = NONE /\
  op_taint a.po_taint cond = {}
Proof
  strip_tac >>
  drule ptr_gap_ownership_history >> strip_tac >>
  drule ptr_chrono_history_reachable >> strip_tac >>
  gvs[ptr_observation_reachable_def] >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >> gvs[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >>
     metis_tac[lookup_block_MEM, MEM_EL]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  (conj_tac
  >- (`~MEM a.po_inst.inst_opcode [ASSIGN; PHI; RET; RETFMP; DRET]` by fs[MEM] >>
      drule_all ptr_nonopaque_instruction_operands >> simp[EVERY_MEM]) >>
  reverse conj_tac
  >- (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  Cases_on `cond` >> simp[op_prov_def] >>
  rename1 `FLOOKUP TG v = NONE` >>
  Cases_on `FLOOKUP TG v` >> simp[] >>
  `v IN fn_pv P a.po_fn` by metis_tac[ptr_source_tagged_var_support] >>
  `ptr_use_ok P (fn_pv P a.po_fn) a.po_inst` by
    (fs[fn_ptr_ok_def] >> metis_tac[]) >>
  fs[MEM] >> gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
      mem_write_ops_def, mem_read_ops_def] >> metis_tac[])
QED

Theorem ptr_history_mixed_eval_phis[local]:
  !insts s t t'.
  ptr_mixed_vars births positions TG tn f g s t /\ ptr_history_content tn s t /\
  s.vs_prev_bb = t.vs_prev_bb /\ retpc_shape_ok f /\
  EVERY (\i. MEM i (fn_insts f) /\ inst_wf i) insts /\
  eval_phis t insts = OK t' ==>
  ?s'. eval_phis s insts = OK s' /\
    ptr_mixed_vars births positions (phis_prov s.vs_prev_bb TG insts)
      (tn with t_var := phis_taint s.vs_prev_bb tn insts) f g s' t' /\
    ptr_history_content tn s' t'
Proof
  Induct
  >- (simp[eval_phis_def, phis_prov_def, phis_taint_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode <> PHI`
  >- (gvs[eval_phis_def, phis_prov_def, phis_taint_def] >>
      qexists_tac `s` >> simp[]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `OPTREL (\(out,sv) (out',tv). out = out' /\
      if retpc_var f out then
        sv = s.vs_return_pc_token /\ tv = t.vs_return_pc_token
      else ptr_value_transport births positions (phi_prov s.vs_prev_bb TG h)
        (phi_taint s.vs_prev_bb tn h) sv tv)
    (eval_one_phi s h) (eval_one_phi t h)` by
    (irule ptr_mixed_eval_one_phi >> gvs[] >> metis_tac[]) >>
  gvs[eval_phis_def, AllCaseEqs()] >>
  gvs[optionTheory.OPTREL_def] >> PairCases_on `x0` >> gvs[] >>
  rename1 `eval_one_phi s h = SOME (out,sv)` >>
  `h.inst_outputs = [out]` by gvs[eval_one_phi_def, AllCaseEqs()] >>
  first_x_assum (qspecl_then [`s`,`t`,`s''`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `u` strip_assume_tac) >>
  qexists_tac `update_var out sv u` >>
  conj_tac >- metis_tac[] >>
  reverse conj_tac >- simp[] >>
  simp[phis_prov_def, phis_taint_def] >>
  irule ptr_mixed_vars_update >>
  rpt (goal_assum (drule_at Any)) >>
  reverse (rpt conj_tac)
  >- metis_tac[]
  >- (imp_res_tac eval_phis_only_updates_vs_vars >>
      qpat_x_assum `u = _` SUBST1_TAC >>
      qpat_x_assum `s'' = _` SUBST1_TAC >>
      Cases_on `retpc_var f out` >> gvs[]) 
  >- (Cases_on `phi_prov t.vs_prev_bb TG h` >>
      gvs[set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
          FLOOKUP_DRESTRICT, op_taint_def] >>
      Cases_on `retpc_var f out` >> gvs[]) >>
  rpt strip_tac >>
  Cases_on `phi_prov t.vs_prev_bb TG h` >>
  simp[set_prov_def, set_var_taint_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >>
  qpat_x_assum `ptr_mixed_vars births positions TG tn f g s t` kall_tac >>
  drule_all ptr_mixed_vars_lookup >> simp[op_taint_def]
QED

Theorem ptr_history_mixed_enters_block[local]:
  g.fn_blocks = (concretize_function_with_positions p f).fn_blocks /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  MEM bb f.fn_blocks /\ bb_well_formed bb /\
  EVERY inst_wf bb.bb_instructions /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  retpc_shape_ok f /\ ptr_mixed_vars births positions TG tn f g s t /\
  ptr_history_content tn s t /\ enters_block g t t' ==>
  ?s'. enters_block f s s' /\
    ptr_mixed_vars births positions (phis_prov s.vs_prev_bb TG bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions) f g s' t' /\
    ptr_history_content tn s' t' /\ s'.vs_current_bb = t'.vs_current_bb /\
    s'.vs_prev_bb = t'.vs_prev_bb
Proof
  rpt strip_tac >>
  `lookup_block t.vs_current_bb g.fn_blocks = SOME
    (clear_nops_block (block_map_transform (concretize_inst_with_positions p) bb))` by
    (qpat_x_assum `g.fn_blocks = _` SUBST1_TAC >>
     simp[concretize_positions_blocks, lookup_block_map,
          concretize_positions_block_label] >> metis_tac[]) >>
  qpat_x_assum `enters_block g t t'` mp_tac >>
  simp[enters_block_def] >> strip_tac >> gvs[] >>
  `eval_phis t bb.bb_instructions = OK s_phi` by
    metis_tac[ptr_positions_block_eval_phis] >>
  `EVERY (\i. MEM i (fn_insts f) /\ inst_wf i) bb.bb_instructions` by
    (fs[EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  drule_all ptr_history_mixed_eval_phis >> strip_tac >>
  qexists_tac `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  conj_tac >- (simp[enters_block_def] >> metis_tac[]) >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  `s'.vs_current_bb = s.vs_current_bb /\
   s_phi.vs_current_bb = t.vs_current_bb /\
   s'.vs_prev_bb = s.vs_prev_bb /\ s_phi.vs_prev_bb = t.vs_prev_bb` by
    (qpat_x_assum `s' = _` SUBST1_TAC >>
     qpat_x_assum `s_phi = _` SUBST1_TAC >> simp[]) >>
  gvs[ptr_mixed_vars_def, ptr_opaque_env_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem ptr_paired_selected_jump_entry[local]:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts a.po_fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp a.po_fn) (Allocation inst.inst_id))) /\
  active_inst at.po_fn at.po_inst at.po_state /\
  is_terminator at.po_inst.inst_opcode /\
  sj = jump_to lbl a.po_state /\ t_jump = jump_to lbl at.po_state /\
  ~t_jump.vs_halted /\ enters_block at.po_fn t_jump t_entry /\
  active_inst at.po_fn it t_entry /\
  bt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn t_jump at.po_prov)
    (entry_taint_vars at.po_fn t_jump at.po_taint) at.po_fn it t_entry ==>
  ?s_entry b bb.
    ~sj.vs_halted /\ enters_block a.po_fn sj s_entry /\
    lookup_block sj.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
    active_inst a.po_fn b.po_inst s_entry /\
    b = ptr_observe a.po_stack a.po_params
      (entry_prov a.po_fn sj a.po_prov)
      (entry_taint_vars a.po_fn sj a.po_taint) a.po_fn b.po_inst s_entry /\
    ptr_paired_cursor lp b bt /\
    ptr_mixed_vars births positions (entry_prov a.po_fn sj TG)
      b.po_taint a.po_fn at.po_fn s_entry t_entry /\
    ptr_history_content b.po_taint s_entry t_entry
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn sj t_jump /\
   ptr_history_content a.po_taint sj t_jump /\
   sj.vs_current_bb = t_jump.vs_current_bb /\
   sj.vs_prev_bb = t_jump.vs_prev_bb /\ ~sj.vs_halted` by
    (fs[ptr_paired_sample_def, ptr_paired_cursor_def] >>
     gvs[jump_to_def, ptr_mixed_vars_def,
         ptr_opaque_env_def, ptr_history_content_def, ptr_taint_content_def,
         ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
         contract_storage_def, contract_transient_def, lookup_var_def] >> metis_tac[]) >>
  `?bb. lookup_block sj.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
    (qpat_x_assum `enters_block _ _ _` mp_tac >>
     fs[ptr_paired_code_def] >>
     simp[enters_block_def, concretize_positions_blocks, lookup_block_map,
          concretize_positions_block_label] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  `MEM bb a.po_fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `at.po_fn.fn_blocks =
    (concretize_function_with_positions (lp a.po_fn) a.po_fn).fn_blocks` by
    fs[ptr_paired_code_def] >>
  drule_all ptr_history_mixed_enters_block >> strip_tac >>
  qmatch_assum_rename_tac `enters_block a.po_fn sj se` >>
  qabbrev_tac `ae = ptr_observe a.po_stack a.po_params
    (entry_prov a.po_fn sj a.po_prov)
    (entry_taint_vars a.po_fn sj a.po_taint) a.po_fn a.po_inst se` >>
  `?i. active_inst a.po_fn i se /\
       ptr_paired_cursor lp (ae with po_inst := i) bt` by
    (irule (INST_TYPE [alpha |-> ``:num``] ptr_paired_entry_cursor) >>
     simp[Abbr `ae`, ptr_observe_def] >>
     qexistsl_tac [`R`,`positions`,`sj`,`t_jump`] >> simp[]) >>
  qexistsl_tac [`se`,`ae with po_inst := i`,`bb`] >>
  simp[Abbr `ae`, ptr_observe_def] >>
  gvs[entry_prov_def, entry_taint_vars_def] >> metis_tac[]
QED

Theorem ptr_paired_jump_entry:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = JMP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts a.po_fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp a.po_fn) (Allocation inst.inst_id))) /\
  active_inst at.po_fn at.po_inst at.po_state /\
  is_terminator at.po_inst.inst_opcode /\
  step_inst fuel Ct at.po_inst at.po_state = OK t_jump /\
  ~t_jump.vs_halted /\ enters_block at.po_fn t_jump t_entry /\
  active_inst at.po_fn it t_entry /\
  bt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn t_jump at.po_prov)
    (entry_taint_vars at.po_fn t_jump at.po_taint) at.po_fn it t_entry ==>
  ?s_jump s_entry b bb.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ~s_jump.vs_halted /\ enters_block a.po_fn s_jump s_entry /\
    lookup_block s_jump.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
    active_inst a.po_fn b.po_inst s_entry /\
    b = ptr_observe a.po_stack a.po_params
      (entry_prov a.po_fn s_jump a.po_prov)
      (entry_taint_vars a.po_fn s_jump a.po_taint) a.po_fn b.po_inst s_entry /\
    ptr_paired_cursor lp b bt /\
    ptr_mixed_vars births positions (entry_prov a.po_fn s_jump TG)
      b.po_taint a.po_fn at.po_fn s_entry t_entry /\
    ptr_history_content b.po_taint s_entry t_entry
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  `at.po_inst = a.po_inst` by
    (simp[concretize_positions_terminator, is_terminator_def]) >>
  `?lbl. a.po_inst.inst_operands = [Label lbl] /\
    t_jump = jump_to lbl at.po_state` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_def, step_inst_base_def] >>
     namedCases_on `a.po_inst.inst_operands` ["", "x xs"] >> simp[] >>
     Cases_on `x` >> simp[] >>
     Cases_on `xs` >> simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `t_jump = jump_to lbl ts` >>
  qabbrev_tac `sj = jump_to lbl a.po_state` >>
  `step_inst fuel C a.po_inst a.po_state = OK sj` by
    simp[Abbr `sj`, step_inst_def, step_inst_base_def] >>
  `sj = jump_to lbl a.po_state /\ t_jump = jump_to lbl at.po_state` by
    simp[Abbr `sj`, Abbr `ts`] >>
  qunabbrev_tac `ts` >>
  drule_all ptr_paired_selected_jump_entry >> strip_tac >>
  qexists_tac `sj` >> metis_tac[]
QED

Theorem ptr_paired_jnz_entry:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = JNZ /\
  a.po_inst.inst_operands = [cond; Label yes; Label no] /\
  ptr_nonopaque_operand a.po_fn cond /\
  op_prov TG cond = NONE /\ op_taint a.po_taint cond = {} /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts a.po_fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp a.po_fn) (Allocation inst.inst_id))) /\
  active_inst at.po_fn at.po_inst at.po_state /\
  is_terminator at.po_inst.inst_opcode /\
  step_inst fuel Ct at.po_inst at.po_state = OK t_jump /\
  ~t_jump.vs_halted /\ enters_block at.po_fn t_jump t_entry /\
  active_inst at.po_fn it t_entry /\
  bt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn t_jump at.po_prov)
    (entry_taint_vars at.po_fn t_jump at.po_taint) at.po_fn it t_entry ==>
  ?s_jump s_entry b bb.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ~s_jump.vs_halted /\ enters_block a.po_fn s_jump s_entry /\
    lookup_block s_jump.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
    active_inst a.po_fn b.po_inst s_entry /\
    b = ptr_observe a.po_stack a.po_params
      (entry_prov a.po_fn s_jump a.po_prov)
      (entry_taint_vars a.po_fn s_jump a.po_taint) a.po_fn b.po_inst s_entry /\
    ptr_paired_cursor lp b bt /\
    ptr_mixed_vars births positions (entry_prov a.po_fn s_jump TG)
      b.po_taint a.po_fn at.po_fn s_entry t_entry /\
    ptr_history_content b.po_taint s_entry t_entry
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  `at.po_inst = a.po_inst` by
    simp[concretize_positions_terminator, is_terminator_def] >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_vars_eval >>
  simp[ptr_lookup_transport_def, ptr_value_transport_def] >>
  strip_tac >>
  `eval_operand cond a.po_state = eval_operand cond at.po_state` by
    (Cases_on `eval_operand cond a.po_state` >>
     Cases_on `eval_operand cond at.po_state` >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  `?v. eval_operand cond at.po_state = SOME v /\
    t_jump = jump_to (if v <> 0w then yes else no) at.po_state` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_def, step_inst_base_def] >>
     Cases_on `eval_operand cond at.po_state` >> simp[] >>
     IF_CASES_TAC >> simp[] >> metis_tac[]) >>
  qabbrev_tac `lbl = if v <> 0w then yes else no` >>
  qabbrev_tac `sj = jump_to lbl a.po_state` >>
  `step_inst fuel C a.po_inst a.po_state = OK sj` by
    (simp[step_inst_def, step_inst_base_def, Abbr `sj`, Abbr `lbl`] >>
     IF_CASES_TAC >> simp[]) >>
  `sj = jump_to lbl a.po_state` by simp[Abbr `sj`] >>
  drule_all ptr_paired_selected_jump_entry >> strip_tac >>
  qexists_tac `sj` >> metis_tac[]
QED

Theorem ptr_paired_jump_entry_overlay:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  a.po_inst.inst_opcode = JMP /\
  step_inst fuel C a.po_inst a.po_state = OK sj /\
  enters_block a.po_fn sj se /\
  b = ptr_observe a.po_stack a.po_params
    (entry_prov a.po_fn sj a.po_prov)
    (entry_taint_vars a.po_fn sj a.po_taint) a.po_fn i se ==>
  ptr_birth_overlay (HD (ptr_activation_tokens h a b tokens))
    b.po_state.vs_allocas births = births
Proof
  strip_tac >>
  `ptr_birth_overlay (HD tokens) a.po_state.vs_allocas births = births` by
    (qpat_x_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_paired_prefix_def] >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_ownership >>
     metis_tac[ptr_ownership_overlay_fixed]) >>
  `sj.vs_allocas = a.po_state.vs_allocas` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_def, step_inst_base_def] >>
     namedCases_on `a.po_inst.inst_operands` ["", "x xs"] >> simp[] >>
     Cases_on `x` >> simp[] >> Cases_on `xs` >> simp[] >>
     rpt strip_tac >> gvs[jump_to_def]) >>
  `se.vs_allocas = sj.vs_allocas` by metis_tac[enters_block_allocas] >>
  gvs[ptr_observe_def, ptr_activation_tokens_def]
QED

Theorem ptr_paired_djmp_entry:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  opaque_use_ok a.po_fn /\ a.po_inst.inst_opcode = DJMP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions /\
  EVERY bb_well_formed a.po_fn.fn_blocks /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!inst. MEM inst (fn_insts a.po_fn) /\ inst.inst_opcode = ALLOCA ==>
    IS_SOME (FLOOKUP (lp a.po_fn) (Allocation inst.inst_id))) /\
  active_inst at.po_fn at.po_inst at.po_state /\
  is_terminator at.po_inst.inst_opcode /\
  step_inst fuel Ct at.po_inst at.po_state = OK t_jump /\
  ~t_jump.vs_halted /\ enters_block at.po_fn t_jump t_entry /\
  active_inst at.po_fn it t_entry /\
  bt = ptr_observe at.po_stack at.po_params
    (entry_prov at.po_fn t_jump at.po_prov)
    (entry_taint_vars at.po_fn t_jump at.po_taint) at.po_fn it t_entry ==>
  ?s_jump s_entry b bb.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ~s_jump.vs_halted /\ enters_block a.po_fn s_jump s_entry /\
    lookup_block s_jump.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
    active_inst a.po_fn b.po_inst s_entry /\
    b = ptr_observe a.po_stack a.po_params
      (entry_prov a.po_fn s_jump a.po_prov)
      (entry_taint_vars a.po_fn s_jump a.po_taint) a.po_fn b.po_inst s_entry /\
    ptr_paired_cursor lp b bt /\
    ptr_mixed_vars births positions (entry_prov a.po_fn s_jump TG)
      b.po_taint a.po_fn at.po_fn s_entry t_entry /\
    ptr_history_content b.po_taint s_entry t_entry
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  `at.po_inst = a.po_inst` by
    simp[concretize_positions_terminator, is_terminator_def] >>
  `?cond ops idx labels. a.po_inst.inst_operands = cond::ops /\
    eval_operand cond at.po_state = SOME idx /\ extract_labels ops = SOME labels /\
    w2n idx < LENGTH labels /\ t_jump = jump_to (EL (w2n idx) labels) at.po_state` by
    (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
     simp[step_inst_def, step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  `ptr_source_ownership vs0 C h a tokens registry births PT TG saved` by
    (drule ptr_paired_prefix_transcript >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_ownership >> simp[]) >>
  `ptr_nonopaque_operand a.po_fn cond /\ op_prov TG cond = NONE /\
    op_taint a.po_taint cond = {}` by
    (`MEM a.po_inst.inst_opcode [JNZ; DJMP] /\ MEM cond a.po_inst.inst_operands` by simp[] >>
     drule_all ptr_owned_jnz_scalar >> simp[]) >>
  `a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
    a.po_state at.po_state` by fs[ptr_paired_sample_def] >>
  drule_all ptr_mixed_vars_eval >>
  simp[ptr_lookup_transport_def, ptr_value_transport_def] >> strip_tac >>
  `eval_operand cond a.po_state = eval_operand cond at.po_state` by
    (Cases_on `eval_operand cond a.po_state` >>
     Cases_on `eval_operand cond at.po_state` >>
     gvs[word_agree_except_bits, fcpTheory.CART_EQ]) >>
  qabbrev_tac `sj = jump_to (EL (w2n idx) labels) a.po_state` >>
  `step_inst fuel C a.po_inst a.po_state = OK sj` by
    simp[step_inst_def, step_inst_base_def, Abbr `sj`] >>
  `sj = jump_to (EL (w2n idx) labels) a.po_state` by simp[Abbr `sj`] >>
  drule_all ptr_paired_selected_jump_entry >> strip_tac >>
  qexists_tac `sj` >> metis_tac[]
QED
