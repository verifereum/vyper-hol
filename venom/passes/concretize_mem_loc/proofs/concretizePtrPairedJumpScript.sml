Theory concretizePtrPairedJump
Ancestors
  concretizePtrPairedJumpEntry concretizePtrPairedPrefixProbe concretizePtrPairedPrefix
  concretizePtrPairedFields concretizePtrSourceOwnership concretizePtrActivationBirths
  concretizePtrStructuralTranscript concretizePtrStructuralTrace concretizePtrEventEmbedding
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  concretizePtrMixedPhi concretizeStepStructure concretizeStepShape
  concretizeStepRetpc concretizeStageShape
  concretizePtrLedgerAlignment concretizePtrDeletedGapHistory ptrDisciplineEmptyTaint
  passSimulationDefs contextCodegenRel venomExecProofs venomState venomInst
  venomExecSemantics venomWf unitShapeDefs ptrDiscipline finite_map list rich_list arithmetic

Theorem ptr_paired_control_fields[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\
  step_inst fuel C inst s = OK t ==>
  t.vs_params = s.vs_params /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> fs[MEM] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_def, step_inst_base_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), jump_to_def]
QED

Theorem ptr_paired_block_prefix_normalize[local]:
  ptr_paired_prefix R lp positions lo vs0 C Ct
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP] /\
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
    (entry_taint_vars at.po_fn t_jump at.po_taint) at.po_fn it t_entry /\
  step_inst fuel C a.po_inst a.po_state = OK sj /\
  ~sj.vs_halted /\ enters_block a.po_fn sj se /\
  lookup_block sj.vs_current_bb a.po_fn.fn_blocks = SOME source_bb /\
  active_inst a.po_fn b.po_inst se /\
  b = ptr_observe a.po_stack a.po_params
    (entry_prov a.po_fn sj a.po_prov)
    (entry_taint_vars a.po_fn sj a.po_taint) a.po_fn b.po_inst se /\
  ptr_paired_cursor lp b bt /\
  ptr_mixed_vars births positions (entry_prov a.po_fn sj TG)
    b.po_taint a.po_fn at.po_fn se t_entry /\
  ptr_history_content b.po_taint se t_entry ==>
  ?s_jump b B TG' bb n delta snapshots.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
    TG' = entry_prov a.po_fn s_jump TG /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1]) tokens registry B PT TG' saved entries
      ((H ++ [(tokens,registry,B,PT,TG',saved,entries)]) ++ snapshots) calls ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp a.po_fn)
      (ptr_gap_scan bb n b).po_inst /\
    (ptr_gap_scan bb n b).po_prov = b.po_prov /\
    (ptr_gap_scan bb n b).po_taint = b.po_taint
Proof
  strip_tac >>
  rename1 `enters_block a.po_fn s_jump s_entry` >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  `b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
   bt.po_fn = at.po_fn /\ bt.po_stack = at.po_stack` by
    (qpat_x_assum `b = _` mp_tac >>
     simp[ptr_observe_def, ptr_observation_component_equality] >>
     metis_tac[]) >>
  `at.po_inst = a.po_inst` by
    (fs[MEM] >> simp[concretize_positions_terminator, is_terminator_def]) >>
  `MEM at.po_inst.inst_opcode [JMP; JNZ; DJMP]` by metis_tac[] >>
  `t_jump.vs_params = at.po_state.vs_params` by
    metis_tac[ptr_paired_control_fields] >>
  `s_jump.vs_params = a.po_state.vs_params /\
   s_jump.vs_allocas = a.po_state.vs_allocas` by
    metis_tac[ptr_paired_control_fields] >>
  `ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births = births` by
    (`ptr_birth_overlay (HD tokens) a.po_state.vs_allocas births = births` by
       (qpat_x_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
        simp[ptr_paired_prefix_def] >> strip_tac >>
        drule ptr_structural_transcript_erasure >> strip_tac >>
        drule ptr_structural_trace_ownership >>
        metis_tac[ptr_ownership_overlay_fixed]) >>
     `s_entry.vs_allocas = s_jump.vs_allocas` by
       metis_tac[enters_block_allocas] >>
     qpat_x_assum `b = _` mp_tac >>
     simp[ptr_observe_def, ptr_observation_component_equality] >> metis_tac[]) >>
  qpat_x_assum `at.po_inst = a.po_inst` kall_tac >>
  `ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT
     (entry_prov a.po_fn s_jump TG) saved` by
    (suspend "tagged") >>
  `ptr_chrono_step Ct at bt` by (suspend "target") >>

  `ptr_paired_prefix R lp positions lo vs0 C Ct
    (h ++ [b]) b (ht ++ [bt]) bt (done ++ [LENGTH h - 1])
    tokens registry births PT (entry_prov a.po_fn s_jump TG) saved entries
    (H ++ [(tokens,registry,births,PT,entry_prov a.po_fn s_jump TG,saved,entries)])
    calls ws` by (suspend "prefix") >>
  `fn_inst_wf b.po_fn` by simp[] >>
  drule_all ptr_paired_prefix_normalize >> strip_tac >>
  qexistsl_tac [`s_jump`,`b`,`births`,`entry_prov a.po_fn s_jump TG`,
    `bb`,`n`,`delta`,`snapshots`] >> simp[]
QED

Resume ptr_paired_block_prefix_normalize[tagged]:
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
     simp[ptr_paired_cursor_def] >> strip_tac >>
     drule ptr_ledger_alignment_cursor >> strip_tac >>
     `at.po_state.vs_inst_idx < LENGTH bbt.bb_instructions` by gvs[] >>
     first_x_assum drule >> strip_tac >>
     simp[active_inst_def] >> qexists_tac `bb` >>
     `bb.bb_label = a.po_state.vs_current_bb` by metis_tac[lookup_block_label] >>
     simp[] >> metis_tac[LESS_EQ_LESS_TRANS]) >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  `ptr_tagged_chrono_step C (HD tokens)
    (ptr_observe a.po_stack a.po_params a.po_prov a.po_taint a.po_fn a.po_inst a.po_state)
    (ptr_observe a.po_stack a.po_params (entry_prov a.po_fn s_jump a.po_prov)
      (entry_taint_vars a.po_fn s_jump a.po_taint) a.po_fn b.po_inst s_entry)
    PT TG saved PT (entry_prov a.po_fn s_jump TG) saved` by
    (irule (cj 2 ptr_tagged_chrono_step_rules) >>
     fs[MEM, is_terminator_def] >> metis_tac[]) >>
  metis_tac[]
QED
Resume ptr_paired_block_prefix_normalize[target]:
  `ptr_observe at.po_stack at.po_params at.po_prov at.po_taint
    at.po_fn at.po_inst at.po_state = at` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  `ptr_chrono_step Ct
    (ptr_observe at.po_stack at.po_params at.po_prov at.po_taint
      at.po_fn at.po_inst at.po_state) bt` by
    (qpat_x_assum `bt = _` SUBST1_TAC >>
     irule (cj 2 ptr_chrono_step_rules) >> metis_tac[]) >>
  metis_tac[]
QED
Resume ptr_paired_block_prefix_normalize[prefix]:
  qpat_x_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_paired_prefix_def]) >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `EVERY (\n. SUC n < LENGTH h) done` by
    (drule ptr_structural_trace_embedding >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  rewrite_tac[ptr_paired_prefix_def] >>
  conj_tac >- suspend "transcript" >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "samples" >>
  conj_tac >- suspend "alignment" >>
  conj_tac >- (irule ptr_paired_callers_retained >>
    gvs[ptr_paired_samples_def, ptr_sample_list_def] >>
    qexistsl_tac [`a`,`at`] >> simp[]) >>
  suspend "writes"
QED
Resume ptr_paired_block_prefix_normalize[transcript]:
  `a.po_inst.inst_id = at.po_inst.inst_id` by
    simp[concretize_positions_inst_id] >>
  `LENGTH b.po_stack = LENGTH a.po_stack /\
   LENGTH bt.po_stack = LENGTH at.po_stack` by simp[] >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED
Resume ptr_paired_block_prefix_normalize[samples]:
  irule ptr_paired_samples_pair >> simp[ptr_paired_sample_def] >>
  qpat_x_assum `b = _` mp_tac >> qpat_x_assum `bt = _` mp_tac >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  rpt strip_tac >> gvs[]
QED
Resume ptr_paired_block_prefix_normalize[alignment]:
  irule ptr_paired_alignment_pair >> simp[] >>
  `s_entry.vs_params = s_jump.vs_params /\
   t_entry.vs_params = t_jump.vs_params` by
    (fs[enters_block_def] >>
     imp_res_tac eval_phis_only_updates_vs_vars >>
     qpat_x_assum `s_phi' = _` (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_params`) >>
     qpat_x_assum `s_phi = _` (mp_tac o Q.AP_TERM `\s:venom_state. s.vs_params`) >>
     simp[]) >>
  qpat_x_assum `b = _` mp_tac >> qpat_x_assum `bt = _` mp_tac >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  rpt strip_tac >> gvs[ptr_paired_params_def]
QED
Resume ptr_paired_block_prefix_normalize[writes]:
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  irule (SRULE [] (Q.SPECL [`ws`,`[]`] ptr_paired_writes_pair)) >>
  gvs[ptr_paired_samples_def, ptr_sample_list_def, MEM, is_terminator_def]
QED
Finalise ptr_paired_block_prefix_normalize


Theorem ptr_paired_jump_prefix_normalize:
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
  ?s_jump b B TG' bb n delta snapshots.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
    TG' = entry_prov a.po_fn s_jump TG /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1]) tokens registry B PT TG' saved entries
      ((H ++ [(tokens,registry,B,PT,TG',saved,entries)]) ++ snapshots) calls ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp a.po_fn)
      (ptr_gap_scan bb n b).po_inst /\
    (ptr_gap_scan bb n b).po_prov = b.po_prov /\
    (ptr_gap_scan bb n b).po_taint = b.po_taint
Proof
  strip_tac >> drule_all ptr_paired_jump_entry >> strip_tac >>
  `MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  drule_all ptr_paired_block_prefix_normalize >> simp[]
QED

Theorem ptr_paired_jnz_prefix_normalize:
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
  ?s_jump b B TG' bb n delta snapshots.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
    TG' = entry_prov a.po_fn s_jump TG /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1]) tokens registry B PT TG' saved entries
      ((H ++ [(tokens,registry,B,PT,TG',saved,entries)]) ++ snapshots) calls ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp a.po_fn)
      (ptr_gap_scan bb n b).po_inst /\
    (ptr_gap_scan bb n b).po_prov = b.po_prov /\
    (ptr_gap_scan bb n b).po_taint = b.po_taint
Proof
  strip_tac >> drule_all ptr_paired_jnz_entry >> strip_tac >>
  `MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  drule_all ptr_paired_block_prefix_normalize >> simp[]
QED

Theorem ptr_paired_djmp_prefix_normalize:
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
  ?s_jump b B TG' bb n delta snapshots.
    step_inst fuel C a.po_inst a.po_state = OK s_jump /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
    TG' = entry_prov a.po_fn s_jump TG /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    lookup_block b.po_state.vs_current_bb b.po_fn.fn_blocks = SOME bb /\
    LENGTH delta = n /\ LENGTH snapshots = n /\
    ptr_paired_prefix R lp positions lo vs0 C Ct
      ((h ++ [b]) ++ delta) (ptr_gap_scan bb n b) (ht ++ [bt]) bt
      (done ++ [LENGTH h - 1]) tokens registry B PT TG' saved entries
      ((H ++ [(tokens,registry,B,PT,TG',saved,entries)]) ++ snapshots) calls ws /\
    (ptr_gap_scan bb n b).po_inst.inst_opcode <> NOP /\
    bt.po_inst = concretize_inst_with_positions (lp a.po_fn)
      (ptr_gap_scan bb n b).po_inst /\
    (ptr_gap_scan bb n b).po_prov = b.po_prov /\
    (ptr_gap_scan bb n b).po_taint = b.po_taint
Proof
  strip_tac >> drule_all ptr_paired_djmp_entry >> strip_tac >>
  `MEM a.po_inst.inst_opcode [JMP; JNZ; DJMP]` by simp[] >>
  drule_all ptr_paired_block_prefix_normalize >> simp[]
QED
