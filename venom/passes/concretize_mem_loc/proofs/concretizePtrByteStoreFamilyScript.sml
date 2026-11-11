(*
 * Paired-prefix extension for the N8 opcode family (MSTORE8; ISTORE).
 *)
Theory concretizePtrByteStoreFamily
Ancestors
  concretizePtrStorageReadProducer ptrDiscipline concretizePtrRequestHistory
  concretizePtrTaintContent concretizePtrOpaqueRetpc concretizePtrSharedFields
  venomExecSemantics venomState finite_map concretizePtrStoreSteps
  venomMemProps regularCallEmitSim pointerConfinedDefs memLocDefs
  concretizePtrValueTransport concretizePtrPairedPrefix concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrChronologicalHistory
  concretizePtrDeletedGapHistory concretizePtrLedgerProbe concretizePtrLedgerAlignment
  concretizePtrPrefixLedger concretizePtrDeletedGaps concretizePtrAllocationSize
  concretizePtrSourceOwnership concretizePtrPairedFields o1PassContract
  o1ScheduleDecomp venomWf cfgWf unitShapeDefs concretizeStepStructure opcodeClass venomInst list arithmetic
  passSimulationDefs venomExecProofs unitLabelMapIdentity contextCodegenRel codegenRel
  concretizeMemLocDefs concretizePtrActivationChronology
  concretizePtrHistoricalWriteClassification concretizePtrTaggedSupport
  concretizePtrEventEmbedding concretizePtrBytes concretizePtrComparisonTransport
  concretizePtrOrdinaryNext concretizePtrPairedPrefixProbe
  concretizePtrOperationalOpcodes

Theorem ptr_byte_store_mstore8_operands_untainted:
  taint_ok fn tn inst s /\ inst.inst_opcode = MSTORE8 ==>
  !op. MEM op inst.inst_operands ==> op_taint tn op = {}
Proof
  strip_tac >> gvs[taint_ok_def] >> metis_tac[]
QED

Theorem ptr_byte_store_history_istore:
  ptr_history_content tn s t /\ word_agree_except m u v ==>
  ptr_history_content (tn with t_imm := key_update tn.t_imm k m)
    (istore k u s) (istore k v t)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def,
    ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
    istore_def, mstore_def, contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> gvs[FLOOKUP_UPDATE, key_update_def] >>
  Cases_on `k = k'` >> gvs[]
QED

Theorem ptr_byte_store_istore_operands_no_provenance:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ISTORE /\
  (!x. x IN FDOM TG ==> x IN fn_pv P fn) /\
  MEM op inst.inst_operands ==> op_prov TG op = NONE
Proof
  strip_tac >>
  `!v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  Cases_on `op` >> gvs[op_prov_def] >> metis_tac[flookup_thm]
QED

Theorem ptr_byte_store_mstore8_history:
  ptr_history_content tn s t ==>
  ptr_history_content tn (mstore8 off u s) (mstore8 offt v t)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def,
    ptr_taint_control_def, ptr_core_shared_def, ptr_shared_fields_def,
    mstore8_def, contract_storage_def, contract_transient_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ptr_byte_store_mstore8_written_byte:
  (w2w u : word8) = w2w v ==>
  read_byte off (mstore8 off u s).vs_memory =
  read_byte offt (mstore8 offt v t).vs_memory
Proof
  simp[mstore8_eq_write_mem, read_byte_write_memory_with_expansion]
QED

Theorem ptr_byte_store_istore_written_bytes:
  k < 32 /\ EL k (word_to_bytes u T) = EL k (word_to_bytes v T) ==>
  read_byte (off + k) (istore off u s).vs_memory =
  read_byte (offt + k) (istore offt v t).vs_memory
Proof
  strip_tac >> rewrite_tac[istore_memory] >>
  irule ptr_mstore_written_bytes >> simp[]
QED

Theorem ptr_byte_store_mstore8_value_no_provenance:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [a;v] /\
  (!x. x IN FDOM TG ==> x IN fn_pv P fn) ==>
  op_prov TG v = NONE
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P fn) inst` by
    (gvs[fn_ptr_ok_def] >> metis_tac[]) >>
  `!x. v = Var x ==> x NOTIN fn_pv P fn` by
    (rpt strip_tac >>
     gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
       mem_write_ops_def, mem_read_ops_def] >>
     first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
     strip_tac >> gvs[] >> strip_tac >> gvs[]) >>
  Cases_on `v` >> gvs[op_prov_def] >> metis_tac[flookup_thm]
QED

Theorem ptr_byte_store_istore_step_content:
  ptr_history_content tn s t /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME addr /\
  word_agree_except (op_taint tn v) u ut ==>
  ptr_history_content (step_taint inst s (istore (w2n addr) u s) tn)
    (istore (w2n addr) u s) (istore (w2n addr) ut t)
Proof
  strip_tac >>
  irule ptr_history_content_masks >>
  qexists_tac `tn with t_imm := key_update tn.t_imm (w2n addr) (op_taint tn v)` >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def] >>
  irule ptr_byte_store_history_istore >> simp[]
QED

Theorem ptr_byte_store_mstore8_step_content:
  ptr_history_content tn s t /\ inst.inst_opcode = MSTORE8 ==>
  ptr_history_content (step_taint inst s (mstore8 off u s) tn)
    (mstore8 off u s) (mstore8 offt v t)
Proof
  strip_tac >> irule ptr_history_content_masks >> qexists_tac `tn` >>
  simp[step_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    ptr_byte_store_mstore8_history]
QED

Theorem ptr_byte_store_istore_mixed_execution:
  fn_ptr_ok P f /\ MEM inst (fn_insts f) /\
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\
  (!x. x IN FDOM TG ==> x IN fn_pv P f) /\
  taint_ok f tn inst s /\
  ptr_mixed_vars births positions (TG : string |-> num # num) tn f g s t /\
  ptr_history_content tn s t /\
  ptr_nonopaque_operand f a /\ ptr_nonopaque_operand f v /\
  exec_write2 (\a v s. istore (w2n a) v s) inst t = OK tt ==>
  ?ss. exec_write2 (\a v s. istore (w2n a) v s) inst s = OK ss /\
    ptr_mixed_vars births positions TG (step_taint inst s ss tn) f g ss tt /\
    ptr_history_content (step_taint inst s ss tn) ss tt
Proof
  strip_tac >>
  `op_prov TG a = NONE /\ op_prov TG v = NONE` by
    (conj_tac >> irule ptr_byte_store_istore_operands_no_provenance >>
     metis_tac[listTheory.MEM]) >>
  `op_taint tn a = {}` by
    (spose_not_then assume_tac >>
     fs[taint_ok_def] >>
     first_x_assum (qspec_then `a` mp_tac) >> simp[] >>
     strip_tac >> gvs[]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `ptr_lookup_transport births positions NONE {} (eval_operand a s) (eval_operand a t) /\
   ptr_lookup_transport births positions NONE (op_taint tn v)
      (eval_operand v s) (eval_operand v t)` by
    (metis_tac[ptr_mixed_vars_eval]) >>
  gvs[exec_write2_def, AllCaseEqs(), ptr_lookup_transport_some_right,
      ptr_value_transport_scalar_empty] >>
  conj_tac
  >- (irule ptr_mixed_vars_fields >>
      qexistsl_tac [`s`,`t`,`tn`] >>
      simp[istore_def, mstore_def, step_taint_def, store_taint_def,
           imm_taint_def, adopt_reset_def, set_var_taint_def, DRESTRICT_UNIV]) >>
  irule ptr_byte_store_istore_step_content >>
  gvs[ptr_value_transport_def]
QED

Theorem ptr_byte_store_mstore8_mixed_execution:
  fn_ptr_ok P f /\ MEM inst (fn_insts f) /\
  inst.inst_opcode = MSTORE8 /\ inst.inst_operands = [a;v] /\
  inst.inst_outputs = [] /\
  (!x. x IN FDOM TG ==> x IN fn_pv P f) /\
  taint_ok f tn inst s /\
  ptr_mixed_vars births positions (TG : string |-> num # num) tn f g s t /\
  ptr_history_content tn s t /\ ptr_nonopaque_operand f v /\
  exec_write2 (\a v s. mstore8 (w2n a) v s) inst t = OK tt ==>
  ?addr u. eval_operand a s = SOME addr /\ eval_operand v s = SOME u /\
    eval_operand v t = SOME u /\
    exec_write2 (\a v s. mstore8 (w2n a) v s) inst s =
      OK (mstore8 (w2n addr) u s) /\
    ptr_mixed_vars births positions TG
      (step_taint inst s (mstore8 (w2n addr) u s) tn) f g
      (mstore8 (w2n addr) u s) tt /\
    ptr_history_content (step_taint inst s (mstore8 (w2n addr) u s) tn)
      (mstore8 (w2n addr) u s) tt
Proof
  strip_tac >>
  `op_prov TG v = NONE` by
    (irule ptr_byte_store_mstore8_value_no_provenance >> metis_tac[]) >>
  `op_taint tn v = {}` by
    (metis_tac[ptr_byte_store_mstore8_operands_untainted, listTheory.MEM]) >>
  `s.vs_labels = t.vs_labels` by metis_tac[ptr_history_content_labels] >>
  `ptr_lookup_transport births positions NONE {}
      (eval_operand v s) (eval_operand v t)` by
    metis_tac[ptr_mixed_vars_eval] >>
  drule_all ptr_mixed_vars_eval_presence >> strip_tac >>
  gvs[exec_write2_def, AllCaseEqs(), ptr_lookup_transport_some_right,
      ptr_value_transport_scalar_empty] >>
  Cases_on `eval_operand a s`
  >- (first_x_assum (qspec_then `a` mp_tac) >> simp[]) >>
  gvs[] >> conj_tac
  >- (irule ptr_mixed_vars_fields >> qexistsl_tac [`s`,`t`,`tn`] >>
      simp[mstore8_def, step_taint_def, store_taint_def, imm_taint_def,
           adopt_reset_def, set_var_taint_def, DRESTRICT_UNIV]) >>
  irule ptr_byte_store_mstore8_step_content >> simp[]
QED

Theorem ptr_byte_store_istore_masked_written_bytes:
  inst.inst_opcode = ISTORE /\ inst.inst_operands = [a;v] /\
  eval_operand a s = SOME addr /\
  word_agree_except (op_taint tn v) u ut /\ k < 32 /\
  w2n addr + k NOTIN
    (step_taint inst s (istore (w2n addr) u s) tn).t_mem ==>
  read_byte (w2n addr + k) (istore (w2n addr) u s).vs_memory =
  read_byte (offt + k) (istore offt ut t).vs_memory
Proof
  strip_tac >> irule ptr_byte_store_istore_written_bytes >> simp[] >>
  `k NOTIN op_taint tn v` by
    (gvs[step_taint_def, mem_taint_def, written_taint_def,
         store_taint_def, adopt_reset_def] >>
     first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  metis_tac[word_agree_except_def]
QED

Theorem ptr_byte_store_transcript_successor:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  MEM a.po_inst.inst_opcode [MSTORE8; ISTORE] /\ ptr_chrono_step C' at zt ==>
  ?z. ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    z.po_state.vs_allocas = a.po_state.vs_allocas /\ z.po_stack = a.po_stack
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `inst_wf a.po_inst` by suspend "shape" >>
  `a.po_inst.inst_outputs = []` by (fs[listTheory.MEM] >> gvs[inst_wf_def]) >>
  `at.po_inst = a.po_inst` by suspend "aligned" >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> fs[listTheory.MEM] >> gvs[is_terminator_def]
  >- suspend "operands"
  >- suspend "operands"
  >> qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac
  >> simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED

Resume ptr_byte_store_transcript_successor[shape]:
  gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >>
     gvs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  fs[fn_inst_wf_def, EVERY_MEM, fn_insts_MEM] >> metis_tac[]
QED

Resume ptr_byte_store_transcript_successor[aligned]:
  qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
  simp[ptr_paired_cursor_def] >> strip_tac >>
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     qpat_x_assum `a.po_inst = _` SUBST_ALL_TAC >> fs[listTheory.MEM]) >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
  strip_tac >> gvs[concretize_inst_with_positions_def, listTheory.MEM]
QED

Resume ptr_byte_store_transcript_successor[operands]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
    AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `a.po_inst.inst_operands = [op1;op2]` >>
  `ptr_mixed_vars births positions TG a.po_taint a.po_fn at.po_fn
     a.po_state at.po_state /\ a.po_state.vs_labels = at.po_state.vs_labels` by
    (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
  drule_all ptr_mixed_vars_eval_presence >>
  disch_then (fn th => map_every (mp_tac o C Q.SPEC th) [`op1`,`op2`]) >>
  simp[] >> rpt strip_tac >>
  Cases_on `eval_operand op1 a.po_state` >> gvs[] >>
  Cases_on `eval_operand op2 a.po_state` >> gvs[] >>
  qabbrev_tac `post = if a.po_inst.inst_opcode = MSTORE8 then
    mstore8 (w2n x) x' a.po_state else istore (w2n x) x' a.po_state` >>
  `?i. active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx)` by
    suspend "source_cursor" >>
  `step_inst 0 C a.po_inst a.po_state = OK post` by
    simp[Abbr `post`, step_inst_non_invoke, step_inst_base_def, exec_write2_def] >>
  qabbrev_tac `z = ptr_ledger_next a i post` >>
  `z.po_stack = a.po_stack /\ z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[Abbr `z`, Abbr `post`, ptr_ledger_next_def, ptr_observe_def,
         mstore8_def, istore_def, mstore_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` by
    suspend "tagged_step" >>
  qexists_tac `z` >> simp[] >>
  drule ptr_ownership_overlay_fixed >> strip_tac >>
  drule (cj 3 ptr_structural_transcript_rules) >>
  disch_then drule >> disch_then drule >>
  simp[ptr_activation_tokens_def, ptr_activation_registry_def]
QED

Resume ptr_byte_store_transcript_successor[source_cursor]:
  markerLib.RESUME_TAC >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `bb_well_formed bb` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >> metis_tac[]) >>
  `SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx = LENGTH bb.bb_instructions - 1` by decide_tac >>
     `LAST bb.bb_instructions = a.po_inst` by
       (fs[bb_well_formed_def] >> metis_tac[LAST_EL, PRE_SUB1]) >>
     gvs[bb_well_formed_def, is_terminator_def]) >>
  simp[Abbr `post`, active_inst_def, mstore8_def, istore_def, mstore_def] >>
  qexists_tac `bb` >> simp[]
QED

Resume ptr_byte_store_transcript_successor[tagged_step]:
  markerLib.RESUME_TAC >>
  `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG` by
    simp[ptr_tagged_step_def, step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE` by
    simp[is_terminator_def] >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  fs[Abbr `z`, ptr_ledger_next_def] >> metis_tac[]
QED

Finalise ptr_byte_store_transcript_successor

Theorem ptr_byte_store_write_producer:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  MEM a.po_inst.inst_opcode [MSTORE8; ISTORE] /\ ptr_chrono_step C' at zt ==>
  ?z reloc.
    ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
      (done ++ [LENGTH h - 1]) tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    z.po_state.vs_allocas = a.po_state.vs_allocas /\ z.po_stack = a.po_stack /\
    ptr_paired_write lo positions C C' (h ++ [z]) (ht ++ [zt])
      (done ++ [LENGTH h - 1])
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)])
      (LENGTH h - 1,LENGTH done,reloc)
Proof
  strip_tac >>
  drule_all ptr_byte_store_transcript_successor >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> metis_tac[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (gvs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `access_ok lo a.po_prov a.po_fn a.po_inst a.po_state /\
   taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[listTheory.MEM]) >>
  suspend "setup"
QED

Resume ptr_byte_store_write_producer[setup]:
  `at.po_inst = a.po_inst` by suspend "aligned" >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!x. x IN FDOM TG ==> x IN fn_pv P a.po_fn` by
    (rpt strip_tac >>
     `?tag. FLOOKUP TG x = SOME tag` by metis_tac[FLOOKUP_DEF] >>
     drule_all ptr_source_tagged_var_support >> simp[]) >>
  `ptr_stage_placements C' positions` by fs[ptr_paired_prefix_def] >>
  qpat_assum `ptr_structural_transcript R vs C C' h a ht at done tokens registry births PT TG saved entries H`
    (mp_tac o MATCH_MP ptr_structural_transcript_endpoint) >> strip_tac >>
  `EL (LENGTH h - 1) H = (tokens,registry,births,PT,TG,saved,entries)` by
    (`H <> []` by (Cases_on `H` >> gvs[]) >>
     qpat_x_assum `LAST H = _` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `EL (LENGTH h - 1) h = a` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >>
     qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  qpat_assum `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved` mp_tac >>
  once_rewrite_tac[ptr_tagged_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality] >>
  strip_tac >> fs[listTheory.MEM] >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ C _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >> rename1 `a.po_inst.inst_operands = [op1;op2]` >>
  suspend "classify"
QED

Resume ptr_byte_store_write_producer[aligned]:
  qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
  simp[ptr_paired_cursor_def] >> strip_tac >>
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     qpat_x_assum `a.po_inst = _` SUBST_ALL_TAC >> fs[listTheory.MEM]) >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
  strip_tac >> gvs[concretize_inst_with_positions_def, listTheory.MEM]
QED

Resume ptr_byte_store_write_producer[classify]:
  markerLib.RESUME_TAC >> (
  rename1 `eval_operand op1 a.po_state = SOME addr` >>
  `~in_revert_forward a.po_fn a.po_state` by suspend "nonrevert" >>
  `ptr_lookup_transport births positions (op_prov TG op1) (op_taint a.po_taint op1)
    (eval_operand op1 a.po_state) (eval_operand op1 at.po_state) /\
   ptr_lookup_transport births positions (op_prov TG op2) (op_taint a.po_taint op2)
    (eval_operand op2 a.po_state) (eval_operand op2 at.po_state)` by
    (conj_tac >>
     (irule ptr_mixed_vars_eval >> conj_tac
      >- (fs[ptr_paired_sample_def] >> metis_tac[ptr_history_content_labels]) >>
      qexistsl_tac [`a.po_fn`,`at.po_fn`] >> fs[ptr_paired_sample_def])) >>
  qabbrev_tac `len:num = if a.po_inst.inst_opcode = MSTORE8 then 1 else 32` >>
  qabbrev_tac `ops = <|iao_ofst := op1; iao_size := SOME (Lit (n2w len));
    iao_max_size := SOME (Lit (n2w len))|>` >>
  `mem_write_ops a.po_inst = SOME ops` by simp[Abbr `ops`, Abbr `len`, mem_write_ops_def] >>
  `MEM (w2n addr,len) (source_memory_write_ranges a.po_inst a.po_state)` by
    simp[Abbr `len`, source_memory_write_ranges_def, fixed_source_write_range_def,
         mem_write_ops_def] >>
  `EL (LENGTH h - 1) h = a` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_end >> strip_tac >>
     qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `len <> 0` by simp[Abbr `len`] >>
  `(op_prov TG ops.iao_ofst = NONE /\
    op_taint (EL (LENGTH h - 1) h).po_taint ops.iao_ofst = {} /\ w2n addr + len <= lo) \/
   (?dv token bid db sb pb. ops.iao_ofst = Var dv /\ FLOOKUP TG dv = SOME (token,bid) /\
    FLOOKUP (EL (LENGTH h - 1) h).po_prov dv = SOME (db,sb) /\
    FLOOKUP positions (Allocation bid) = SOME (pb,sb) /\ db <= w2n addr /\
    w2n addr + len <= db+sb /\ pb+sb < dimword(:256))` by
    (irule ptr_historical_write_classification >> simp[Abbr `ops`] >>
     conj_tac >- (qexists_tac `a.po_fn` >> simp[]) >>
     rpt (goal_assum (drule_at Any)) >> simp[Abbr `len`])
  >- suspend "fixed" >> suspend "owned")
QED

Resume ptr_byte_store_write_producer[nonrevert]:
  markerLib.RESUME_TAC >>
  `ALL_DISTINCT (fn_labels a.po_fn)` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `active_inst a.po_fn a.po_inst a.po_state` mp_tac >>
  simp[active_inst_def] >> strip_tac >>
  `lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[fn_labels_def]) >>
  `get_instruction bb a.po_state.vs_inst_idx = SOME a.po_inst` by simp[get_instruction_def] >>
  simp[in_revert_forward_def] >> strip_tac >>
  drule_all memSafeRunTheory.revert_forward_at_opcode >> simp[]
QED

Resume ptr_byte_store_write_producer[fixed]:
  markerLib.RESUME_TAC >> (
  fs[Abbr `ops`, Abbr `len`] >>
  qpat_x_assum `w2n addr + _ <= lo` mp_tac >> simp[] >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht` by decide_tac >>
  `EL (LENGTH done) ht = at` by
    (`LENGTH ht - 1 = LENGTH done` by decide_tac >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  qexistsl_tac [`z`,`\x:num. x`] >> simp[] >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
        fixed_source_write_range_def, range_bytes_def, pred_setTheory.EXTENSION] >>
      qexists_tac `w2n addr` >> simp[]) >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def,
        source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
      rpt strip_tac >> disj1_tac >> decide_tac) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "fixed_bytes") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()])
QED

Resume ptr_byte_store_write_producer[fixed_bytes]:
  markerLib.RESUME_TAC >> (
  `op_prov TG op2 = NONE` by
    (Cases_on `a.po_inst.inst_opcode = MSTORE8`
     >- (fs[] >> irule ptr_byte_store_mstore8_value_no_provenance >> metis_tac[]) >>
     fs[] >> irule ptr_byte_store_istore_operands_no_provenance >>
     qexistsl_tac [`P`,`a.po_fn`,`a.po_inst`] >> simp[]) >>
  `op_taint a.po_taint op1 = {}` by metis_tac[] >>
  `eval_operand op1 at.po_state = SOME addr` by
    (qpat_x_assum `ptr_lookup_transport _ _ NONE _ _ _` mp_tac >>
     simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  `ptr_chrono_step C a z` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def] >>
  conj_tac
  >- simp[step_writes_def, source_memory_write_ranges_def, fixed_source_write_range_def] >>
  Cases_on `a.po_inst.inst_opcode = MSTORE8`
  >- suspend "mstore8_fixed_bytes" >>
  suspend "istore_fixed_bytes")
QED

Resume ptr_byte_store_write_producer[mstore8_fixed_bytes]:
  markerLib.RESUME_TAC >> fs[] >>
  `op_taint a.po_taint op2 = {}` by
    (metis_tac[ptr_byte_store_mstore8_operands_untainted, listTheory.MEM]) >>
  `eval_operand op2 at.po_state = eval_operand op2 a.po_state` by
    (qpat_x_assum `ptr_lookup_transport _ _ _ _ (eval_operand op2 _) _` mp_tac >>
     simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  simp[ptr_bytes_agree_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, range_bytes_def] >> rpt strip_tac >>
  rename1 `x < w2n daddr + 1` >>
  `x = w2n daddr` by decide_tac >>
  qpat_x_assum `mstore8 _ _ _ = s'` (SUBST_ALL_TAC o SYM) >>
  fs[] >>
  irule ptr_byte_store_mstore8_written_byte >> simp[]
QED

Resume ptr_byte_store_write_producer[istore_fixed_bytes]:
  markerLib.RESUME_TAC >> fs[] >>
  rename1 `eval_operand op1 a.po_state = SOME daddr` >>
  rename1 `eval_operand op2 a.po_state = SOME u` >>
  rename1 `eval_operand op2 at.po_state = SOME ut` >>
  `word_agree_except (op_taint a.po_taint op2) u ut` by
    (qpat_x_assum `ptr_lookup_transport _ _ _ _ (eval_operand op2 _) _` mp_tac >>
     simp[ptr_lookup_transport_def, ptr_value_transport_def]) >>
  qpat_x_assum `istore _ _ _ = s'` (SUBST_ALL_TAC o SYM) >>
  simp[ptr_bytes_agree_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, range_bytes_def] >> rpt strip_tac >>
  `x = w2n daddr + (x - w2n daddr)` by decide_tac >>
  `x - w2n daddr < 32` by decide_tac >>
  qpat_x_assum `x = w2n daddr + _` (fn th => once_rewrite_tac[th]) >>
  irule (SRULE [] ptr_byte_store_istore_masked_written_bytes) >> simp[] >>
  qexistsl_tac [`op1`,`a.po_inst`,`a.po_taint`,`op2`] >> simp[]
QED

Resume ptr_byte_store_write_producer[owned]:
  markerLib.RESUME_TAC >> (
  fs[Abbr `ops`, Abbr `len`] >>
  `a.po_inst.inst_opcode = MSTORE8` by
    (Cases_on `a.po_inst.inst_opcode = MSTORE8` >> fs[] >>
     `op_prov TG (Var dv) = NONE` by
       (irule ptr_byte_store_istore_operands_no_provenance >>
        qexistsl_tac [`P`,`a.po_fn`,`a.po_inst`] >> simp[]) >>
     fs[op_prov_def]) >>
  fs[] >> suspend "mstore8_owned")
QED

Resume ptr_byte_store_write_producer[mstore8_owned]:
  markerLib.RESUME_TAC >> fs[] >>
  qpat_x_assum `w2n addr + _ <= db + sb` mp_tac >> simp[] >> strip_tac >>
  `MEM token tokens` by
    (drule_all ptr_source_ownership_live_prov >> simp[]) >>
  `FLOOKUP births (token,bid) = SOME (db,sb)` by
    (drule_all ptr_source_ownership_prov_erases >>
     simp[ptr_ledger_erases_def] >> strip_tac >>
     first_x_assum (qspec_then `dv` mp_tac) >> gvs[]) >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `SUC (LENGTH h - 1) = LENGTH h /\ SUC (LENGTH done) = LENGTH ht` by decide_tac >>
  `EL (LENGTH done) ht = at` by
    (`LENGTH ht - 1 = LENGTH done` by decide_tac >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  qexistsl_tac [`z`,`\x:num. pb + (x - db)`] >> simp[] >>
  simp[ptr_paired_write_def, EL_APPEND_EQN] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
        fixed_source_write_range_def, range_bytes_def, pred_setTheory.EXTENSION] >>
      qexists_tac `w2n addr` >> simp[]) >>
  reverse conj_tac
  >- (simp[ptr_paired_write_owner_def, step_writes_def,
        source_memory_write_ranges_def, fixed_source_write_range_def, range_bytes_def] >>
      rpt strip_tac >> disj2_tac >>
      qexistsl_tac [`token`,`bid`,`db`,`sb`,`pb`,`x-db`] >> simp[] >> decide_tac) >>
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "mstore8_owned_bytes") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]
QED

Resume ptr_byte_store_write_producer[mstore8_owned_bytes]:
  markerLib.RESUME_TAC >>
  `op_prov TG op2 = NONE` by
    (irule ptr_byte_store_mstore8_value_no_provenance >> metis_tac[]) >>
  `op_taint a.po_taint op2 = {}` by
    (metis_tac[ptr_byte_store_mstore8_operands_untainted, listTheory.MEM]) >>
  `val' = val` by
    (qpat_x_assum `ptr_lookup_transport _ _ _ _ (eval_operand op2 _) _` mp_tac >>
     simp[ptr_lookup_transport_def, ptr_value_transport_scalar_empty]) >>
  `addr' = addr - n2w db + n2w pb` by
    gvs[ptr_lookup_transport_def, ptr_value_transport_def, op_prov_def] >>
  `w2n addr' = pb + (w2n addr - db)` by
    (irule ptr_closed_relocation_value >> simp[] >> qexists_tac `sb` >> simp[] >> decide_tac) >>
  qpat_x_assum `addr' = addr - n2w db + n2w pb` kall_tac >>
  `ptr_chrono_step C a z` by
    (drule ptr_tagged_chrono_step_projection >> simp[]) >>
  simp[ptr_ledger_write_pair_def, is_terminator_def] >>
  conj_tac
  >- (simp[step_writes_def, source_memory_write_ranges_def,
           fixed_source_write_range_def, range_bytes_def] >>
      rpt strip_tac >> decide_tac) >>
  simp[ptr_bytes_agree_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, range_bytes_def] >>
  rpt strip_tac >>
  `x = w2n addr /\ pb + (x - db) = w2n addr'` by decide_tac >>
  qpat_x_assum `mstore8 _ _ _ = s'` (SUBST_ALL_TAC o SYM) >>
  fs[] >>
  `pb + w2n addr - db = w2n addr'` by decide_tac >>
  asm_rewrite_tac[] >> irule ptr_byte_store_mstore8_written_byte >> simp[]
QED

Finalise ptr_byte_store_write_producer

Theorem ptr_paired_prefix_byte_store:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\ fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  MEM a.po_inst.inst_opcode [MSTORE8; ISTORE] /\ ptr_chrono_step C' at zt ==>
  ?z reloc. ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG saved entries
    (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls
    (ws ++ [(LENGTH h - 1,LENGTH done,reloc)])
Proof
  strip_tac >> drule_all ptr_byte_store_write_producer >> strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_source >> strip_tac >>
  drule ptr_structural_trace_target >> strip_tac >>
  drule ptr_structural_trace_embedding >> strip_tac >>
  `LAST h = a /\ LAST ht = at /\ 0 < LENGTH h /\ LENGTH ht = SUC (LENGTH done)` by
    (imp_res_tac ptr_chrono_history_end >>
     fs[ptr_paired_prefix_def, ptr_paired_samples_def, ptr_sample_list_def]) >>
  `EL (LENGTH h - 1) h = a /\ EL (LENGTH done) ht = at` by
    (`h <> [] /\ ht <> []` by (conj_tac >> strip_tac >> gvs[]) >>
     conj_tac
     >- (qpat_x_assum `LAST h = a` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
     `LENGTH ht - 1 = LENGTH done` by decide_tac >>
     qpat_x_assum `LAST ht = at` mp_tac >> simp[LAST_EL, PRE_SUB1]) >>
  `SUC (LENGTH h - 1) = LENGTH h` by decide_tac >>
  `ptr_ledger_write_pair C C' reloc a z at zt` by
    (qpat_assum `ptr_paired_write _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ptr_paired_write_def]) >>
     gvs[EL_APPEND_EQN]) >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
      a.po_fn a.po_inst a.po_state` by
    (qpat_x_assum `ptr_chrono_history vs C' ht at` kall_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `MEM a.po_fn C.ctx_functions` by (drule_all ptr_frame_sizes >> simp[]) >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (qpat_x_assum `frame_reachable _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Once frame_reachable_cases] >> rpt strip_tac >>
     gvs[active_inst_def, fn_insts_MEM] >> metis_tac[lookup_block_MEM, MEM_EL]) >>
  `at.po_inst = a.po_inst` by suspend "aligned" >>
  `a.po_inst.inst_outputs = [] /\ ALL_DISTINCT (fn_labels a.po_fn)` by
    (`inst_wf a.po_inst` by
       (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
           EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
     fs[inst_wf_def, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM, wf_function_def] >>
     gvs[] >> metis_tac[]) >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by
    (fs[ptr_paired_code_def] >> metis_tac[fn_labels_def, concretize_positions_labels]) >>
  `!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
     ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p` by
    (metis_tac[ptr_paired_stage_local_allocas]) >>
  qexistsl_tac [`z`,`reloc`] >>
  qpat_x_assum `ptr_paired_prefix _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ptr_paired_prefix_def]) >>
  rewrite_tac[ptr_paired_prefix_def] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- suspend "sample" >>
  conj_tac >- suspend "alignment" >>
  conj_tac >- suspend "callers" >> suspend "writes"
QED

Resume ptr_paired_prefix_byte_store[aligned]:
  qpat_x_assum `ptr_paired_cursor lp a at` mp_tac >>
  simp[ptr_paired_cursor_def] >> strip_tac >>
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[] >>
     qpat_x_assum `a.po_inst = _` SUBST_ALL_TAC >> fs[listTheory.MEM]) >>
  drule ptr_ledger_alignment_cursor >> strip_tac >>
  first_x_assum (qspec_then `at.po_state.vs_inst_idx` mp_tac) >> simp[] >>
  strip_tac >> gvs[concretize_inst_with_positions_def, listTheory.MEM]
QED
Resume ptr_paired_prefix_byte_store[sample]:
  irule ptr_paired_samples_pair >> simp[] >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `fn_ptr_ok P a.po_fn` by fs[EVERY_MEM] >>
  `EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, fn_inst_wf_def,
        EVERY_MEM, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\fn. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts fn)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!x. x IN FDOM TG ==> x IN fn_pv P a.po_fn` by
    (rpt strip_tac >>
     `?tag. FLOOKUP TG x = SOME tag` by metis_tac[FLOOKUP_DEF] >>
     drule ptr_structural_trace_ownership >> strip_tac >>
     drule_all ptr_source_tagged_var_support >> simp[]) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `opaque_use_ok a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (ptr_nonopaque_operand a.po_fn) a.po_inst.inst_operands` by
    (irule ptr_nonopaque_instruction_operands >> fs[listTheory.MEM]) >>
  `ptr_chrono_step C a z` by fs[ptr_ledger_write_pair_def] >>
  qpat_x_assum `ptr_chrono_step C a z` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  fs[listTheory.MEM] >> (
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def] >>
      strip_tac >> suspend "sample_target") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()])
QED
Resume ptr_paired_prefix_byte_store[sample_target]:
  markerLib.RESUME_TAC >> (
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def] >>
      strip_tac >> suspend "sample_content") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()])
QED
Resume ptr_paired_prefix_byte_store[sample_content]:
  markerLib.RESUME_TAC >> (
  fs[exec_write2_def, AllCaseEqs()] >> gs[] >>
  rename1 `a.po_inst.inst_operands = [op1;op2]` >>
  fs[ptr_paired_sample_def] >>
  Cases_on `a.po_inst.inst_opcode = ISTORE`
  >- suspend "istore_sample" >> suspend "mstore8_sample")
QED
Resume ptr_paired_prefix_byte_store[istore_sample]:
  markerLib.RESUME_TAC >> fs[] >>
  `exec_write2 (\a v s. istore (w2n a) v s) a.po_inst at.po_state = OK s''` by
    simp[exec_write2_def] >>
  drule_all ptr_byte_store_istore_mixed_execution >> strip_tac >>
  `ss = s'` by
    (gs[exec_write2_def]) >> fs[] >>
  irule ptr_mixed_vars_fields >>
  qexistsl_tac [`s'`,`s''`,`step_taint a.po_inst a.po_state s' a.po_taint`] >> simp[]
QED
Resume ptr_paired_prefix_byte_store[mstore8_sample]:
  markerLib.RESUME_TAC >> fs[] >>
  `exec_write2 (\a v s. mstore8 (w2n a) v s) a.po_inst at.po_state = OK s''` by
    simp[exec_write2_def] >>
  drule_all ptr_byte_store_mstore8_mixed_execution >> strip_tac >>
  gs[exec_write2_def] >>
  irule ptr_mixed_vars_fields >>
  qexistsl_tac [`s'`,`s''`,`step_taint a.po_inst a.po_state s' a.po_taint`] >> simp[]
QED
Resume ptr_paired_prefix_byte_store[alignment]:
  `ptr_chrono_step C a z` by fs[ptr_ledger_write_pair_def] >>
  qpat_x_assum `ptr_chrono_step C a z` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >> fs[listTheory.MEM] >> (
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "alignment_target") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()])
QED
Resume ptr_paired_prefix_byte_store[alignment_target]:
  markerLib.RESUME_TAC >> (
  qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
  once_rewrite_tac[ptr_chrono_step_cases] >>
  simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
  strip_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
      strip_tac >> suspend "alignment_finish") >>
  qpat_x_assum `step_inst _ _ _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()])
QED
Resume ptr_paired_prefix_byte_store[alignment_finish]:
  markerLib.RESUME_TAC >> (
  irule ptr_paired_alignment_pair >> simp[] >>
  reverse conj_tac >- gvs[ptr_paired_params_def, istore_def, mstore_def, mstore8_def] >>
  irule ptr_ordinary_next_cursor >>
  simp[] >> qexistsl_tac [`a`,`at`] >>
  gvs[istore_def, mstore_def, mstore8_def])
QED
Resume ptr_paired_prefix_byte_store[callers]:
  `zt.po_stack = at.po_stack` by
    (qpat_assum `ptr_chrono_step C' at zt` mp_tac >>
     once_rewrite_tac[ptr_chrono_step_cases] >> fs[listTheory.MEM] >>
     simp[ptr_observe_def, ptr_observation_component_equality, is_terminator_def] >>
     rpt strip_tac >>
     gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def, AllCaseEqs()]) >>
  irule ptr_paired_callers_retained >> simp[] >>
  conj_tac >- fs[ptr_paired_samples_def, ptr_sample_list_def] >>
  fs[ptr_event_embedding_def, EVERY_EL] >>
  qexistsl_tac [`a`,`at`] >> simp[]
QED
Resume ptr_paired_prefix_byte_store[writes]:
  `EVERY (\n. SUC n < LENGTH h) done` by
    (qpat_assum `ptr_event_embedding h ht (done ++ _)` mp_tac >>
     qpat_assum `SUC (LENGTH h - 1) = LENGTH h` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     simp[ptr_event_embedding_def, EVERY_EL] >> strip_tac >>
     gen_tac >> strip_tac >>
     qpat_x_assum `!i j. _` (qspecl_then [`n`,`LENGTH done`] mp_tac) >>
     simp[EL_APPEND_EQN] >> decide_tac) >>
  irule ptr_paired_writes_pair >>
  gvs[ptr_paired_samples_def, ptr_sample_list_def] >> metis_tac[]
QED
Finalise ptr_paired_prefix_byte_store

Theorem ptr_paired_byte_store_prefix_normalize:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
  EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
    first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
    ALL_DISTINCT (fn_labels f) /\
    (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
  EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) /\
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode <> NOP /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt /\ MEM a.po_inst.inst_opcode [MSTORE8; ISTORE] ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all ptr_paired_prefix_byte_store >> strip_tac >>
  `fn_inst_wf z.po_fn` by
    (qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac ptr_paired_prefix_transcript) >> strip_tac >>
     drule ptr_structural_transcript_erasure >> strip_tac >>
     drule ptr_structural_trace_source >> strip_tac >>
     drule ptr_chrono_history_reachable >> strip_tac >>
     fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_assum `ptr_paired_prefix _ _ _ _ _ _ _ (_ ++ [_]) _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ptr_paired_prefix_normalize) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`[z] ++ delta`, `ptr_gap_scan bb (LENGTH delta) z`,
    `tokens`, `registry`, `births`, `PT`, `TG`, `saved`, `entries`,
    `[(tokens,registry,births,PT,TG,saved,entries)] ++ snapshots`, `calls`,
    `ws ++ [(LENGTH h - 1,LENGTH done,reloc)]`] >>
  simp[APPEND_ASSOC, ptr_gap_scan_fields]
QED

