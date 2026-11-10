Theory concretizeLayoutCanonicalBaseCorridor
Ancestors concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  ptrDiscipline venomExecSemantics venomInst list
  concretizeLayoutPhaseCorridor concretizeLayoutPhaseOrigin frameRankedTerminalCorridor

(* Leaf of the exhaustive base certificate: steps from a corridor witness.
   A corridor holds only ASSIGN and its final REVERT. *)

Theorem canonical_corridor_shape[local]:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INR g) ==>
  ~g.ltp_pending /\ layout_corridor_entry C g s t /\
  get_instruction g.ltp_origin.lbo_source s.vs_inst_idx = SOME i /\
  get_instruction g.ltp_origin.lbo_target t.vs_inst_idx = SOME j /\
  i.inst_opcode = (if g.ltp_remaining = 0 then REVERT else ASSIGN)
Proof
  simp[layout_canonical_step_witness_def, layout_canonical_block_witness_def] >>
  strip_tac >> gvs[] >>
  fs[layout_corridor_entry_def, layout_phase_normalize_def,
     ranked_terminal_entry_def, ranked_terminal_corridor_def] >>
  Cases_on `g.ltp_remaining = 0`
  >- gvs[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem layout_canonical_corridor_success:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INR g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode <> INVOKE /\
  step_inst_base i s = OK post ==>
  ~is_terminator i.inst_opcode /\
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INR g) post tpost
Proof
  strip_tac >> drule canonical_corridor_shape >> strip_tac >>
  Cases_on `g.ltp_remaining`
  >- (gvs[] >>
      qpat_x_assum `step_inst_base i s = OK post` mp_tac >>
      simp[Once step_inst_base_def, AllCaseEqs()]) >>
  `i.inst_opcode = ASSIGN` by gvs[] >>
  conj_tac >- simp[is_terminator_def] >>
  drule_all layout_corridor_assign >> strip_tac >> gvs[] >>
  simp[layout_canonical_success_def] >>
  qexists_tac `INR (g with <|ltp_pending := T; ltp_remaining := n'|>)` >>
  simp[layout_phase_origin_def] >> fs[layout_corridor_entry_def]
QED

Theorem layout_canonical_corridor_exit:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ taint_within D C vs0 /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INR g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode <> INVOKE /\
  step_inst_base i s = r /\ (!p. r <> OK p) /\ (!e. r <> Error e) ==>
  ?r'. step_inst_base j t = r' /\
    layout_canonical_result D lo vs0 C C' q0 es qs ass qend q n r r'
Proof
  strip_tac >> drule canonical_corridor_shape >> strip_tac >>
  Cases_on `g.ltp_remaining = 0`
  >- (`?a post. r = Abort a post` by
        (qpat_x_assum `step_inst_base i s = r` mp_tac >>
         gvs[] >> simp[Once step_inst_base_def, AllCaseEqs()] >>
         metis_tac[]) >>
      gvs[] >> drule_all layout_corridor_revert >>
      disch_then (qspec_then `D` strip_assume_tac) >> gvs[] >>
      simp[layout_canonical_result_def]) >>
  `i.inst_opcode = ASSIGN` by gvs[] >>
  qpat_x_assum `step_inst_base i s = r` mp_tac >>
  simp[Once step_inst_base_def, AllCaseEqs()] >> metis_tac[]
QED
