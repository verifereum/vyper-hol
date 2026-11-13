Theory concretizeLayoutCanonicalBaseMemory
Ancestors concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  ptrDiscipline venomExecSemantics venomInst list
  concretizeLayoutExceptionalEntry concretizeLayoutExceptionalCopy
  concretizeLayoutRankedCorridor concretizeLayoutPhaseCorridor
  concretizeLayoutBlockPairing concretizeStepStructure contextCodegenRel arithmetic
  frameFiniteJointDecoration frameJointTrace concretizeLayoutPhaseOrigin
  frameRelocationEnvironment frameRelocationLocal concretizeLayoutEntryFlags
  concretizeLayoutPhaseLoad concretizeLayoutPhaseCopy concretizeLayoutPhaseIstore
  concretizeLayoutPhaseReaders concretizeLayoutPhaseReadCopy concretizeLayoutPhaseResidual
  concretizeLayoutPhaseTrace concretizeLayoutPhaseSha3 concretizeLayoutPhaseLog
  concretizeLayoutLocalCalldataReaders concretizeLayoutLocalReturn
  frameRelocationBinding venomWf o1PassContract venomState

(* Leaf of the exhaustive base certificate: successful ordinary memory,
   calldata, code-copy, hash and log steps, in the shape of
   layout_canonical_ordinary_nonterm_success. *)

Theorem layout_corridor_pair_from_revert_forward[local]:
  layout_block_pair positions bb bb' k k' /\
  get_instruction bb k = SOME i /\ i.inst_opcode = RETURNDATACOPY /\
  revert_forward_at bb k ==>
  ?n. ranked_terminal_corridor bb bb' (SUC k) (SUC k') n
Proof
  strip_tac >>
  `layout_block_pair positions bb bb' (SUC k) (SUC k')` by
    (drule_all layout_block_pair_advance >>
     simp[concretize_positions_unchanged, ADD1]) >>
  fs[revert_forward_at_def] >-
    (`terminal_corridor bb bb (SUC k) j` by
       (irule layout_revert_forward_corridor >> simp[] >> metis_tac[]) >>
     metis_tac[layout_terminal_corridor_ranked]) >>
  fs[revert_forward_pair_def] >> gvs[]
QED

Theorem layout_canonical_exempt_returncopy_success[local]:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\ decoration_at fn i s q /\
  i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >> drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  `revert_forward_at g.lop_origin.lbo_source s.vs_inst_idx` by
    (qpat_x_assum `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[layout_canonical_step_witness_def, layout_canonical_block_witness_def,
       concretizeLayoutPairedEntryTheory.layout_paired_ordinary_def] >>
     rpt strip_tac >> gvs[decoration_entry_def, decoration_at_def, in_revert_forward_def] >>
     metis_tac[]) >>
  drule_all layout_corridor_pair_from_revert_forward >> strip_tac >>
  `?opd ops opn dst src sz. i.inst_operands = [opd;ops;opn] /\
    eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
    eval_operand opn s = SOME sz` by
    (qpat_x_assum `step_inst_base i s = OK post` mp_tac >>
     simp[step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  `terminal_call_prefix C g.lop_origin.lbo_source g.lop_origin.lbo_entry s /\
   resolved_config_ok g.lop_config g.lop_ids g.lop_anns /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    (gs[layout_ordinary_entry_def, layout_ordinary_trace_def, layout_phase_normalize_def] >>
     metis_tac[]) >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >>
  `resolved_config_ok (JointConfig stk PG G tn fn i s oms om hs h)
    (birth::ids) ((rp,rv)::anns)` by metis_tac[] >>
  drule_all concretize_returncopy_success_complete >> strip_tac >>
  `variable_domains s t` by metis_tac[local_rel_domains] >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  `s.vs_halted = t.vs_halted` by metis_tac[layout_ordinary_entry_halted_agree] >>
  drule_all layout_corridor_copy_entry >> strip_tac >>
  qexists `tpost` >> simp[layout_canonical_success_def] >>
  qexists `INR <|ltp_origin := g.lop_origin; ltp_pending := T; ltp_remaining := n|>` >>
  simp[layout_phase_origin_def] >>
  fs[layout_corridor_entry_def]
QED

Theorem layout_canonical_ordinary_memory_success[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
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
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  MEM i.inst_opcode [MLOAD; MCOPY; ILOAD; ISTORE; CALLDATALOAD; CALLDATASIZE;
    CALLDATACOPY; CODECOPY; EXTCODECOPY; RETURNDATACOPY; DLOADBYTES; SHA3; LOG] /\
  (i.inst_opcode = RETURNDATACOPY ==> ~in_revert_forward fn s) /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >> drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `i.inst_opcode <> ALLOCA /\ i.inst_opcode <> INVOKE /\
   ~is_terminator i.inst_opcode` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >> simp[] >> strip_tac >>
  `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  `inst_wf i` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `~in_revert_forward fn s` by
    (Cases_on `i.inst_opcode = RETURNDATACOPY` >- gvs[] >>
     irule active_inst_not_revert_forward >>
     conj_tac >- fs[o1_fn_shape_def, wf_function_def] >>
     qexists `i` >> fs[decoration_at_def, MEM]) >>
  `~joint_read_exempt (EL g.lop_cursor (q0::MAP SND path))` by
    (fs[layout_ordinary_trace_def] >> metis_tac[joint_read_exempt_def]) >>
  `?k tpost. step_inst_base i t = OK tpost /\ k.lop_pending /\
    k.lop_cursor = SUC g.lop_cursor /\ k.lop_ids = g.lop_ids /\
    resolved_annotation_update g.lop_config (EL g.lop_cursor (MAP FST path))
      g.lop_ids g.lop_anns k.lop_anns /\
    layout_phase_ok_abort D lo vs0 C C' q0 (MAP FST path) (MAP SND path) qend
      (INL g) (INL k) (OK post) (OK tpost)` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >>
     gvs[] >>
     `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
     `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
     FIRST [(`MEM i.inst_opcode [MLOAD; ILOAD]` by simp[] >>
         drule_all layout_word_load_trace_step),
       drule_all layout_mcopy_trace_step, drule_all layout_istore_trace_step,
       (`calldata_reader_shape i` by simp[calldata_reader_shape_def] >>
         drule_all layout_calldata_reader_trace_step),
       (`MEM i.inst_opcode [CALLDATACOPY; CODECOPY; DLOADBYTES]` by simp[] >>
         drule_all layout_readcopy_trace_step), drule_all layout_sha3_trace_step,
       drule_all layout_log_trace_step,
       (qpat_assum `i.inst_opcode = EXTCODECOPY` kall_tac >>
        rename1 `i.inst_operands = [opa;opd;ops;opn]` >>
        `?addr dst src sz. eval_operand opa s = SOME addr /\
          eval_operand opd s = SOME dst /\ eval_operand ops s = SOME src /\
          eval_operand opn s = SOME sz` by
          (qpat_x_assum `step_inst_base i s = OK post` mp_tac >>
           simp[step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
        drule_all layout_extcodecopy_trace_step),
       (qpat_assum `i.inst_opcode = RETURNDATACOPY` kall_tac >>
        rename1 `i.inst_operands = [opd;ops;opn]` >>
        `(?dst src sz. eval_operand opd s = SOME dst /\
          eval_operand ops s = SOME src /\ eval_operand opn s = SOME sz) /\
          post.vs_inst_idx = s.vs_inst_idx` by
          (qpat_x_assum `step_inst_base i s = OK post` mp_tac >>
           simp[step_inst_base_def, AllCaseEqs()] >> rpt strip_tac >>
           gvs[write_memory_with_expansion_def, write_memory_def] >> metis_tac[]) >>
        drule_all layout_returncopy_trace_step)] >> strip_tac >> metis_tac[]) >>
  qexists `tpost` >> conj_tac >- simp[] >>
  drule layout_canonical_ordinary_success >>
  disch_then (qspecl_then [`tpost`, `EL g.lop_cursor (MAP SND path)`, `post`, `k`, `i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem layout_canonical_memory_success:
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
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode <> INVOKE /\
  MEM i.inst_opcode [MLOAD; MCOPY; ILOAD; ISTORE; CALLDATALOAD; CALLDATASIZE;
    CALLDATACOPY; CODECOPY; EXTCODECOPY; RETURNDATACOPY; DLOADBYTES; SHA3; LOG] /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >>
  Cases_on `i.inst_opcode = RETURNDATACOPY /\ in_revert_forward fn s`
  >- (qpat_x_assum `_ /\ in_revert_forward fn s` strip_assume_tac >>
      drule_all layout_canonical_exempt_returncopy_success >> simp[]) >>
  `i.inst_opcode = RETURNDATACOPY ==> ~in_revert_forward fn s` by metis_tac[] >>
  drule_all layout_canonical_ordinary_memory_success >> simp[]
QED
