Theory gasFocusConcretizeCutFrameAccess
Ancestors
  unitMemInv contextRawReachable
  concretizePtrChronologicalHistory concretizePtrForwardingTaintHistory
  concretizePtrOwnerPath concretizePtrOperationalOpcodes
  lowerDloadPtrRawReachable lowerDloadPtrForward contextCodegenRel codegenRel
  o1PassContract o1PassLift o1SafeUpto unitTransformDefs
  venomPassSchedule ptrDiscipline venomWf lowerDloadDefs stackPlanGen
  venomState words list

Theorem focus_concretize_window_opcode[local]:
  ptr_chrono_history vs C h at /\ EVERY wf_function C.ctx_functions /\
  lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j ==>
  at.po_inst.inst_opcode = ASSIGN \/
  (at.po_inst.inst_opcode = REVERT /\ at.po_state.vs_inst_idx = j /\
   in_revert_forward at.po_fn at.po_state)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_chrono_history_reachable >>
  simp[ptr_observation_reachable_def] >> strip_tac >>
  drule ptr_frame_context_membership >> strip_tac >>
  `ALL_DISTINCT (fn_labels at.po_fn)` by fs[EVERY_MEM,wf_function_def] >>
  drule ptr_owner_frame_active >> strip_tac >>
  drule_all active_inst_block_lookup >> strip_tac >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  `get_instruction bb at.po_state.vs_inst_idx = SOME at.po_inst` by gvs[] >>
  `i <= at.po_state.vs_inst_idx` by decide_tac >>
  drule_all revert_forward_pair_interval_opcode >> strip_tac
  >- (qsuff_tac `F` >- simp[] >> decide_tac)
  >- simp[] >>
  simp[in_revert_forward_def, revert_forward_at_def] >>
  qexists `i` >> gvs[]
QED

Theorem focus_concretize_window_frame_access[local]:
  ptr_chrono_history vs C h at /\
  EVERY wf_function C.ctx_functions /\
  EVERY (\fn. EVERY inst_wf (fn_insts fn)) C.ctx_functions /\
  (!b op. MEM b h /\ b.po_inst.inst_opcode = RETURNDATACOPY /\
    MEM op b.po_inst.inst_operands ==> op_taint b.po_taint op = {}) /\
  lookup_block at.po_state.vs_current_bb at.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb i j /\
  i < at.po_state.vs_inst_idx /\ at.po_state.vs_inst_idx <= j ==>
  access_ok eom at.po_prov at.po_fn at.po_inst at.po_state /\
  taint_ok at.po_fn at.po_taint at.po_inst at.po_state
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all focus_concretize_window_opcode >> strip_tac
  >- simp[access_ok_def, taint_ok_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def] >>
  `!op. MEM op at.po_inst.inst_operands ==> op_taint at.po_taint op = {}` by
    metis_tac[ptr_chrono_forward_revert_operands_clean] >>
  simp[access_ok_def, taint_ok_def, about_to_revert_def] >> metis_tac[]
QED

(* Scratch statement for elaboration and independent review.
   The bounded root uses the cut-local headroom premise. The field
   supplier's existing theorem still takes whole-run headroom.
   The available C3 shape is o1_ctx_shape C'. The forwarding window helper
   needs operand cleanliness at each historical RETURNDATACOPY it uses. *)
Theorem focus_concretize_cut_frame_access:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_ctx_shape C' /\ o1_initial_state_ok vs /\
  vs.vs_fmp = vs.vs_initial_fmp /\ code_layout_valid vs /\
  o1_ptr_safe_upto D lo n C vs /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> dload_headroom_ok ctx fn inst s) C vs /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
    raw_mem_ok C fn inst s /\ dload_offset_ok C fn inst s) /\
  alloca_frontier_upto n C vs /\
  EVERY ssa_form C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  max_live_eom C' = SOME eom /\
  (ctx_has_dalloca C ==> eom <= w2n vs.vs_initial_fmp) ==>
  !stk PG G tn fn inst s. frame_reachable vs C' stk PG G tn fn inst s /\
    gas_cut n vs s ==> access_ok eom G fn inst s /\ taint_ok fn tn inst s
Proof
  cheat
QED
