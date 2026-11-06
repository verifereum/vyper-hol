Theory concretizePtrUniversalStepSchema
Ancestors
  concretizePtrMloadProducer concretizePtrPairedCallSchema concretizePtrMixedAllocationPrefix
  concretizePtrPairedJump concretizePtrPairedRoot concretizePtrOwnedAllocationPrefix
  concretizePtrPairedPrefixProbe concretizePtrPairedPrefix concretizePtrPairedFields
  concretizePtrOpaqueRetpc concretizePtrSourceOwnership
  concretizePtrActivationChronology concretizePtrChronologicalHistory
  concretizeStepStructure concretizeStepShape concretizeStepCallChecks
  concretizeStepRetpc concretizeStageShape
  o1PassContract stackPlanGen ptrDiscipline unitMemInv venomWf cfgWf
  o1ScheduleDecomp venomExecSemantics venomInst list finite_map

(* Specification artifacts ONLY: parsing/typechecking these terms proves nothing.
   The explicit production/static bridge premises must be supplied at the stage
   consumer. They are not extra hypotheses proposed for the frozen theorem. *)
val universal_normalized_step_schema = ``
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
  ptr_chrono_step C' at zt ==>
  ?delta z tokens' registry' births' PT' TG' saved' entries' snapshots calls' ws'.
    delta <> [] /\ LENGTH snapshots = LENGTH delta /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ delta) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ snapshots) calls' ws' /\
    z.po_inst.inst_opcode <> NOP /\
    zt.po_inst = concretize_inst_with_positions (lp z.po_fn) z.po_inst
``;

(* First selected structural supplier: actual ALLOCA versus rewritten ASSIGN.
   No source success, unrestricted transport, fresh-only cache, or post-prefix
   certificate is assumed. Full certificate assembly remains a later consumer. *)
val mixed_allocation_success_schema = ``
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
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = ALLOCA /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  ptr_chrono_step C' at zt ==>
  ?s' b B TG'.
    step_inst 0 C a.po_inst a.po_state = OK s' /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_state = (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    TG' = ptr_tagged_step (HD tokens) PT TG a.po_inst s' /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP B owner = SOME site) /\
    ptr_mixed_vars B positions TG' b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state /\
    ptr_core_shared b.po_state zt.po_state /\ ptr_paired_cursor lp b zt
``;

(* Candidate integration interface ONLY; not a proved theorem. Old H entries
   retain their original births/TG; only the appended snapshot uses B/TG'. *)
val mixed_allocation_immediate_prefix_schema = ``
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
  ptr_paired_prefix R lp positions lo vs C C'
    h a ht at done tokens registry births PT TG saved entries H calls ws /\
  a.po_inst.inst_opcode = ALLOCA /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  fn_inst_wf a.po_fn /\ retpc_shape_ok a.po_fn /\
  ptr_chrono_step C' at zt ==>
  ?s' b B TG'.
    step_inst 0 C a.po_inst a.po_state = OK s' /\
    b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\ b.po_params = a.po_params /\
    b.po_state = (s' with vs_inst_idx := SUC a.po_state.vs_inst_idx) /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT TG' saved /\
    TG' = ptr_tagged_step (HD tokens) PT TG a.po_inst s' /\
    B = ptr_birth_overlay (HD tokens) b.po_state.vs_allocas births /\
    (!owner site. FLOOKUP births owner = SOME site ==> FLOOKUP B owner = SOME site) /\
    ptr_mixed_vars B positions TG' b.po_taint b.po_fn zt.po_fn b.po_state zt.po_state /\
    ptr_core_shared b.po_state zt.po_state /\ ptr_paired_cursor lp b zt /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry B PT TG' saved entries
      (H ++ [(tokens,registry,B,PT,TG',saved,entries)]) calls ws
``;

(* RET audit artifact ONLY, not a theorem. Actual target success is the only
   execution premise; source success and the entire immediate certificate are
   conclusions. Normalization is a separate consumer of that certificate. *)
val return_immediate_prefix_schema = ``
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
  a.po_inst.inst_opcode = RET /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?b ret se sr tokens' registry' births' PT' TG' saved' entries' calls' ws'.
    step_inst 0 C a.po_inst a.po_state = IntRet ret se /\
    a.po_stack <> [] /\
    bind_outputs (HD a.po_stack).cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state (HD a.po_stack).cf_state se)) = SOME sr /\
    b.po_state = (sr with vs_inst_idx := SUC (HD a.po_stack).cf_state.vs_inst_idx) /\
    ptr_tagged_chrono_step C (HD tokens) a b PT TG saved PT' TG' saved' /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [b]) b (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens' registry' births' PT' TG' saved' entries'
      (H ++ [(tokens',registry',births',PT',TG',saved',entries')]) calls' ws'
``;

(* MCOPY integration audit ONLY. This term is not an exported theorem.
   Zero-sized writes may use an empty ledger suffix; positive writes must
   contribute their actual paired event. No recovered bytes are premises. *)
val mixed_mcopy_immediate_prefix_schema = ``
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
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom /\
  a.po_inst.inst_opcode = MCOPY /\
  at.po_inst = concretize_inst_with_positions (lp a.po_fn) a.po_inst /\
  ptr_chrono_step C' at zt ==>
  ?z reloc extra.
    step_inst 0 C a.po_inst a.po_state =
      OK (z.po_state with vs_inst_idx := a.po_state.vs_inst_idx) /\
    ptr_tagged_chrono_step C (HD tokens) a z PT TG saved PT TG saved /\
    (extra = [] \/ extra = [(LENGTH h - 1,LENGTH done,reloc)]) /\
    (range_bytes (step_writes a.po_inst a.po_state z.po_state) <> {} ==>
      extra = [(LENGTH h - 1,LENGTH done,reloc)]) /\
    ptr_paired_prefix R lp positions lo vs C C'
      (h ++ [z]) z (ht ++ [zt]) zt (done ++ [LENGTH h - 1])
      tokens registry births PT TG saved entries
      (H ++ [(tokens,registry,births,PT,TG,saved,entries)]) calls (ws ++ extra)
``;

(* Stage bridge candidate ONLY. This quotation asserts no theorem. *)
val stage_paired_bridge_schema = ``
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  mem_inv raw_mem_ok C vs /\
  fixed_region_reserved lo C /\ ptr_discipline lo C vs /\
  EVERY ssa_form C.ctx_functions /\ ~ctx_has_dalloca C /\
  ctx_inst_ids_distinct C /\ (?names. callee_first names C.ctx_functions) /\
  EVERY all_reachable C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ max_live_eom C' = SOME eom ==>
  ?R lp positions.
    ptr_stage_placements C' positions /\
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions C'.ctx_functions /\
    EVERY (\f. fn_inst_wf f /\ retpc_shape_ok f /\ opaque_use_ok f /\
      first_block_no_phi f /\ EVERY bb_well_formed f.fn_blocks /\
      ALL_DISTINCT (fn_labels f) /\
      (!i. MEM i (fn_insts f) /\ i.inst_opcode = ALLOCA ==>
        IS_SOME (FLOOKUP (lp f) (Allocation i.inst_id)))) C.ctx_functions /\
    EVERY (\g. ALL_DISTINCT (fn_labels g)) C'.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name)
``;
