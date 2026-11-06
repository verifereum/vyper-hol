Theory concretizePtrReturnProduction
Ancestors concretizePtrUniversalStepSchema concretizePtrReturnTransport
  concretizePtrOpaqueRetpc
  concretizePtrPairedPrefix contextCodegenRel unitLabelMapIdentity
  concretizePtrTaggedSupport concretizePtrParamSupport concretizePtrStructuralTrace
  concretizePtrStructuralTranscript concretizePtrDeletedGapHistory
  concretizePtrChronologicalHistory concretizeStepStructure
  ptrDiscipline memLocDefs unitShapeDefs o1PassContract venomExecSemantics venomState
  venomInst venomWf pointerConfinedDefs finite_map list pred_set

Theorem ptr_paired_ret_scalar_operands:
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
  ?ops last. a.po_inst.inst_operands = ops ++ [last] /\
    EVERY (\op. ptr_nonopaque_operand a.po_fn op /\
      op_prov TG op = NONE /\ op_taint a.po_taint op = {}) ops
Proof
  strip_tac >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  drule ptr_structural_trace_ownership >> strip_tac >>
  `frame_reachable vs C a.po_stack a.po_params a.po_prov a.po_taint
    a.po_fn a.po_inst a.po_state` by
    (drule ptr_gap_ownership_history >> strip_tac >>
     drule ptr_chrono_history_reachable >> simp[ptr_observation_reachable_def]) >>
  `?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions` by
    (fs[EVERY_MEM, fn_inst_wf_def, fn_insts_MEM] >> metis_tac[]) >>
  `EVERY (\f. EVERY (\i. i.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions` by
    (fs[ctx_has_dalloca_def, EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
  `!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn` by
    (rpt strip_tac >> irule ptr_source_tagged_var_support >>
     rpt (goal_assum (drule_at Any))) >>
  `taint_ok a.po_fn a.po_taint a.po_inst a.po_state` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >>
  `fn_ptr_ok P a.po_fn /\ opaque_use_ok a.po_fn` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `!vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==> active_inst fn inst s` by
    (ho_match_mp_tac frame_reachable_ind >> simp[]) >>
  `active_inst a.po_fn a.po_inst a.po_state` by metis_tac[] >>
  `MEM a.po_inst (fn_insts a.po_fn)` by
    (fs[active_inst_def, fn_insts_MEM] >> metis_tac[EL_MEM]) >>
  `!v. MEM (Var v) a.po_inst.inst_operands ==> v NOTIN fn_pv P a.po_fn` by
    (qpat_x_assum `fn_ptr_ok P a.po_fn` mp_tac >>
     simp[fn_ptr_ok_def] >> strip_tac >>
     qpat_x_assum `!inst. MEM inst (fn_insts a.po_fn) ==> _`
       (qspec_then `a.po_inst` mp_tac) >>
     simp[ptr_use_ok_def, is_pointer_preserving_op_def,
       mem_write_ops_def, mem_read_ops_def] >> metis_tac[]) >>
  `at.po_inst = a.po_inst` by
    (gvs[concretize_positions_unchanged]) >>
  `a.po_inst.inst_operands <> []` by
    (qpat_x_assum `ptr_chrono_step C' at zt` mp_tac >>
     simp[Once ptr_chrono_step_cases, ptr_observe_def] >>
     rpt strip_tac >> gvs[is_terminator_def] >>
     gvs[Once run_defs, step_inst_base_def, AllCaseEqs()] >>
     Cases_on `a.po_inst.inst_operands` >> gvs[eval_operands_def]) >>
  qexistsl_tac [`FRONT a.po_inst.inst_operands`, `LAST a.po_inst.inst_operands`] >>
  simp[APPEND_FRONT_LAST] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM op a.po_inst.inst_operands` by metis_tac[APPEND_FRONT_LAST, MEM_APPEND] >>
  `op_taint a.po_taint op = {}` by
    (qpat_x_assum `taint_ok _ _ _ _` mp_tac >> simp[taint_ok_def] >> metis_tac[]) >>
  `op_prov TG op = NONE` by
    (Cases_on `op` >> simp[op_prov_def] >>
     Cases_on `FLOOKUP TG s` >> simp[] >> metis_tac[]) >>
  simp[] >> Cases_on `op` >> simp[ptr_nonopaque_operand_def] >>
  strip_tac >>
  `retpc_use_ok a.po_inst s` by metis_tac[opaque_use_ok_retpc_use] >>
  gvs[retpc_use_ok_def] >> gvs[rich_listTheory.FRONT_APPEND_NOT_NIL]
QED
