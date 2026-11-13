Theory concretizePtrOrdinaryNext
Ancestors concretizePtrPairedNextAttach concretizePtrLedgerProbe
  concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrStructuralTranscript concretizePtrStructuralTrace
  concretizePtrSourceOwnership concretizePtrChronologicalHistory
  concretizePtrActivationChronology concretizePtrDeletedGapHistory
  concretizePtrTaggedSupport concretizePtrLedgerAlignment
  concretizePtrPrefixLedger concretizePtrStagePlacements concretizePtrDeletedGaps
  concretizePtrExecutedCoverage concretizeStepStructure concretizeStepShape
  o1PassContract unitShapeDefs venomWf cfgWf venomExecSemantics venomState
  ptrDiscipline contextCodegenRel unitLabelMapIdentity venomExecProofs venomInst finite_map list arithmetic

(* The next retained source instruction exists independently of the value
   semantics of the instruction being executed. *)
Theorem ptr_ordinary_next_active:
  active_inst f inst s /\ EVERY bb_well_formed f.fn_blocks /\
  ~is_terminator inst.inst_opcode /\ post.vs_current_bb = s.vs_current_bb ==>
  ?i. active_inst f i (post with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> fs[active_inst_def] >>
  `bb_well_formed bb` by metis_tac[EVERY_MEM] >>
  `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (spose_not_then assume_tac >>
     `s.vs_inst_idx = LENGTH bb.bb_instructions - 1` by decide_tac >>
     `LAST bb.bb_instructions = inst` by
       (fs[bb_well_formed_def] >> metis_tac[LAST_EL, PRE_SUB1]) >>
     gvs[bb_well_formed_def]) >>
  simp[active_inst_def] >> qexists_tac `bb` >> simp[]
QED

Theorem ptr_ordinary_next_cursor:
  ptr_paired_cursor lp a at /\ a.po_inst.inst_opcode <> NOP /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p) /\
  z.po_fn = a.po_fn /\ zt.po_fn = at.po_fn /\
  z.po_state.vs_current_bb = a.po_state.vs_current_bb /\
  zt.po_state.vs_current_bb = at.po_state.vs_current_bb /\
  z.po_state.vs_prev_bb = a.po_state.vs_prev_bb /\
  zt.po_state.vs_prev_bb = at.po_state.vs_prev_bb /\
  z.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx /\
  zt.po_state.vs_inst_idx = SUC at.po_state.vs_inst_idx /\
  active_inst z.po_fn z.po_inst z.po_state /\
  active_inst zt.po_fn zt.po_inst zt.po_state ==>
  ptr_paired_cursor lp z zt
Proof
  strip_tac >> gvs[ptr_paired_cursor_def] >>
  `SUC a.po_state.vs_inst_idx < LENGTH bb.bb_instructions /\
   z.po_inst = EL (SUC a.po_state.vs_inst_idx) bb.bb_instructions` by
    (qpat_assum `active_inst _ z.po_inst _` mp_tac >>
     qpat_assum `z.po_state.vs_current_bb = _` mp_tac >>
     qpat_assum `z.po_state.vs_inst_idx = _` mp_tac >>
     qpat_assum `lookup_block _ a.po_fn.fn_blocks = SOME bb` mp_tac >>
     qpat_assum `a.po_state.vs_current_bb = at.po_state.vs_current_bb` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels a.po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[active_inst_def, fn_labels_def] >> rpt strip_tac >>
     rename1 `MEM nextbb a.po_fn.fn_blocks` >>
     `lookup_block at.po_state.vs_current_bb a.po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  `SUC at.po_state.vs_inst_idx < LENGTH bbt.bb_instructions /\
   zt.po_inst = EL (SUC at.po_state.vs_inst_idx) bbt.bb_instructions` by
    (qpat_assum `active_inst _ zt.po_inst _` mp_tac >>
     qpat_assum `zt.po_state.vs_current_bb = _` mp_tac >>
     qpat_assum `zt.po_state.vs_inst_idx = _` mp_tac >>
     qpat_assum `lookup_block _ at.po_fn.fn_blocks = SOME bbt` mp_tac >>
     qpat_assum `ALL_DISTINCT (fn_labels at.po_fn)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[active_inst_def, fn_labels_def] >> rpt strip_tac >>
     rename1 `MEM nextbb at.po_fn.fn_blocks` >>
     `lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME nextbb` by
       (irule MEM_lookup_block >> simp[]) >> gvs[]) >>
  suspend "order"
QED
Resume ptr_ordinary_next_cursor[order]:
  `a.po_state.vs_inst_idx = EL at.po_state.vs_inst_idx indices` by
    (spose_not_then assume_tac >>
     `a.po_state.vs_inst_idx < EL at.po_state.vs_inst_idx indices` by decide_tac >>
     qpat_x_assum `!k. _ ==> _.inst_opcode = NOP`
       (qspec_then `a.po_state.vs_inst_idx` mp_tac) >> simp[]) >>
  `LENGTH bbt.bb_instructions = LENGTH indices` by
    (drule ptr_ledger_alignment_cursor >> simp[]) >>
  `SUC at.po_state.vs_inst_idx < LENGTH indices` by decide_tac >>
  `EL at.po_state.vs_inst_idx indices < EL (SUC at.po_state.vs_inst_idx) indices` by
    (qpat_assum `ptr_ledger_block_alignment _ _ _ indices` mp_tac >>
     qpat_assum `SUC at.po_state.vs_inst_idx < LENGTH indices` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     irule ptr_ledger_alignment_order >> simp[] >>
     qexistsl_tac [`lp a.po_fn`,`bb.bb_instructions`,`bbt.bb_instructions`] >> simp[]) >>
  qexists_tac `indices` >> simp[] >> rpt strip_tac >>
  `(concretize_inst_with_positions (lp a.po_fn)
      (EL k bb.bb_instructions)).inst_opcode = NOP` by
    (irule ptr_ledger_alignment_gap >>
     qexistsl_tac [`indices`,`SUC at.po_state.vs_inst_idx`,`bbt.bb_instructions`] >>
     simp[] >> decide_tac) >>
  `k < LENGTH bb.bb_instructions` by
    (drule ptr_ledger_alignment_cursor >> strip_tac >>
     `EL (SUC at.po_state.vs_inst_idx) indices < LENGTH bb.bb_instructions` by
       (qpat_x_assum `!j. j < LENGTH bbt.bb_instructions ==> _`
          (qspec_then `SUC at.po_state.vs_inst_idx` mp_tac) >> simp[]) >> decide_tac) >>
  drule_all ptr_positioned_block_nop_iff >> simp[]
QED
Finalise ptr_ordinary_next_cursor

Theorem ptr_paired_stage_local_allocas:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc) view C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\ o1_ctx_shape C /\
  MEM a.po_fn C.ctx_functions ==>
  !ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p
Proof
  strip_tac >> drule ptr_paired_prefix_endpoint >> strip_tac >>
  rpt strip_tac >> drule_all ptr_stage_alloca_mems >> strip_tac >>
  `MEM g C'.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `FLOOKUP positions (Allocation ai.inst_id) =
    SOME (p,get_alloca_size a.po_fn (Allocation ai.inst_id))` by
    (fs[ptr_paired_prefix_def, ptr_stage_placements_def] >> metis_tac[]) >>
  fs[ptr_paired_code_def, fn_insts_MEM] >>
  qpat_x_assum `!bb inst. _` (qspecl_then [`bb`,`ai`] mp_tac) >> simp[]
QED

Theorem ptr_paired_prefix_ordinary_nonwrite:
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  active_inst a.po_fn a.po_inst a.po_state /\
  ~is_terminator a.po_inst.inst_opcode /\ a.po_inst.inst_opcode <> INVOKE /\
  a.po_inst.inst_opcode <> NOP /\
  step_inst fuel C a.po_inst a.po_state = OK post /\
  active_inst a.po_fn i (post with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
  z = ptr_ledger_next a i post /\ ptr_chrono_step C' at zt /\
  zt.po_stack = at.po_stack /\ zt.po_fn = at.po_fn /\
  post.vs_allocas = a.po_state.vs_allocas /\
  post.vs_current_bb = a.po_state.vs_current_bb /\
  post.vs_prev_bb = a.po_state.vs_prev_bb /\
  zt.po_state.vs_current_bb = at.po_state.vs_current_bb /\
  zt.po_state.vs_prev_bb = at.po_state.vs_prev_bb /\
  zt.po_state.vs_inst_idx = SUC at.po_state.vs_inst_idx /\
  active_inst zt.po_fn zt.po_inst zt.po_state /\
  a.po_inst.inst_id = at.po_inst.inst_id /\
  ALL_DISTINCT (fn_labels a.po_fn) /\ ALL_DISTINCT (fn_labels at.po_fn) /\
  (!ai. MEM ai (fn_insts a.po_fn) /\ ai.inst_opcode = ALLOCA ==>
    ?p. FLOOKUP (lp a.po_fn) (Allocation ai.inst_id) = SOME p) /\
  ptr_tagged_step (HD tokens) PT TG a.po_inst z.po_state = TG' /\
  ptr_paired_sample positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
  ptr_paired_params positions z zt (tokens,registry,births,PT,TG',saved,entries) /\
  range_bytes (step_writes a.po_inst a.po_state z.po_state) = {} ==>
  ptr_paired_prefix R lp positions lo vs C C'
    (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
    tokens registry births PT TG' saved entries
    (H ++ [(tokens,registry,births,PT,TG',saved,entries)]) calls ws
Proof
  strip_tac >>
  drule ptr_paired_prefix_endpoint >> strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `z.po_fn = a.po_fn /\ z.po_stack = a.po_stack /\
   z.po_state.vs_allocas = a.po_state.vs_allocas` by
    simp[ptr_ledger_next_def, ptr_observe_def] >>
  `ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG' saved` by
    suspend "tagged" >>
  `ptr_structural_transcript R vs C C' (h ++ [z]) z (ht ++ [zt]) zt
     (done ++ [LENGTH h - 1]) tokens registry births PT TG' saved entries
     (H ++ [(tokens,registry,births,PT,TG',saved,entries)])` by
    (drule ptr_ownership_overlay_fixed >> strip_tac >>
     drule (cj 3 ptr_structural_transcript_rules) >>
     disch_then drule >> disch_then drule >>
     simp[ptr_activation_tokens_def, ptr_activation_registry_def]) >>
  `ptr_paired_cursor lp z zt` by
    (drule ptr_ordinary_next_cursor >> disch_then irule >>
     simp[ptr_ledger_next_def, ptr_observe_def]) >>
  drule ptr_paired_prefix_nonwrite_attach >> disch_then irule >> simp[]
QED
Resume ptr_paired_prefix_ordinary_nonwrite[tagged]:
  `ptr_tagged_step (HD tokens) PT TG a.po_inst post = TG'` by
    gvs[ptr_ledger_next_def, ptr_observe_def, ptr_tagged_step_def, step_prov_def,
        out_prov_def, lookup_var_def] >>
  drule_all (cj 1 ptr_tagged_chrono_step_rules) >> strip_tac >>
  `ptr_observe a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state = a` by
    simp[NoAsms, ptr_observe_def, ptr_observation_component_equality] >>
  fs[ptr_ledger_next_def] >> metis_tac[]
QED
Finalise ptr_paired_prefix_ordinary_nonwrite
