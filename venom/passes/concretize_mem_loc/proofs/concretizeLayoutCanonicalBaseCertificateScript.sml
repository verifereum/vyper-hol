Theory concretizeLayoutCanonicalBaseCertificate
Ancestors concretizeLayoutCanonicalBaseMemory concretizeLayoutCanonicalBaseExternal
  concretizeLayoutCanonicalBaseCorridor concretizeLayoutCanonicalBaseJump
  concretizeLayoutCanonicalBaseTerminalExit concretizeLayoutCanonicalBaseAbortExit
  concretizeLayoutCanonicalBase concretizeLayoutCanonicalDeferred
  concretizeLayoutCanonicalDriver concretizeLayoutSelectedBaseInterface
  concretizeLayoutPhaseCorridor concretizeLayoutPhaseOrigin concretizeLayoutReaderContext
  concretizeStepStructure frameSelectedSimulation frameFiniteExecution
  frameRankedTerminalCorridor frameRelocationCleanValueSteps
  frameRelocationScalarSteps ptrDiscipline venomWf venomExecSemantics venomInst list

(* The exhaustive base-step certificate for the canonical relations, from
   the closed ordinary dispatch and one leaf per remaining family. *)

Theorem layout_canonical_step_witness_not_invoke:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend q n i s j t a /\
  i.inst_opcode <> INVOKE ==> j.inst_opcode <> INVOKE
Proof
  Cases_on `a` >>
  simp[layout_canonical_step_witness_def, layout_canonical_block_witness_def] >>
  strip_tac >> gvs[concretize_positions_not_invoke] >>
  gvs[layout_corridor_entry_def, ranked_terminal_entry_def,
      ranked_terminal_corridor_def, layout_phase_normalize_def] >>
  Cases_on `y.ltp_remaining` >> gvs[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem layout_canonical_result_not_error:
  layout_canonical_result D lo vs0 C C' q0 es qs ass qend qe m r r' ==>
  !e. r' <> Error e
Proof
  Cases_on `r` >> Cases_on `r'` >> simp[layout_canonical_result_def]
QED

Theorem layout_base_opcode_cases[local]:
  inst_wf i /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> DALLOCA /\ i.inst_opcode <> MEMTOP /\
  i.inst_opcode <> GETFMP /\ i.inst_opcode <> SETFMP /\
  i.inst_opcode <> FMP_PARAM /\ i.inst_opcode <> PHI /\
  ~MEM i.inst_opcode [MLOAD; MCOPY; ILOAD; ISTORE; CALLDATALOAD; CALLDATASIZE;
      CALLDATACOPY; CODECOPY; EXTCODECOPY; RETURNDATACOPY; DLOADBYTES; SHA3; LOG] /\
  ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] ==>
  MEM i.inst_opcode [NOP; ALLOCA; ASSIGN; ADD; SUB; SHL; SHR; SAR; OFFSET;
      CALLER; ADDRESS; CALLVALUE; GAS; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; SSTORE;
      TSTORE; EQ; LT; GT; RETURNDATASIZE; ASSERT; ASSERT_UNREACHABLE; MSTORE;
      MSTORE8; BUMP; PARAM; RETPC_PARAM; CODESIZE; DLOAD; INITIAL_FMP; BALANCE;
      SELFBALANCE; EXTCODESIZE; EXTCODEHASH] \/
   context_read0_opcode i.inst_opcode \/
   (clean_value_shape i /\ ~MEM i.inst_opcode [ADD; SUB; EQ; LT; GT])
Proof
  Cases_on `i.inst_opcode` >>
  simp[is_terminator_def, context_read0_opcode_def, clean_value_shape_def,
    scalar_binary_opcode_def, inst_wf_def]
QED

Theorem layout_canonical_base_nonterm_success:
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
    q n i s j t a /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode <> INVOKE /\
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F a post tpost
Proof
  strip_tac >> Cases_on `a`
  >~ [`INR g`] >- (drule_all layout_canonical_corridor_success >> simp[]) >>
  rename1 `INL g` >>
  `MEM fn C.ctx_functions /\ MEM i (fn_insts fn) /\ fn_ptr_ok P fn` by
    (drule_all layout_canonical_ordinary_environment >> strip_tac >> simp[]) >>
  `inst_wf i` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `i.inst_opcode <> DALLOCA` by
    (strip_tac >> fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  `i.inst_opcode <> MEMTOP /\ i.inst_opcode <> GETFMP /\
   i.inst_opcode <> SETFMP /\ i.inst_opcode <> FMP_PARAM` by
    (qpat_x_assum `fn_ptr_ok P fn` mp_tac >> simp[fn_ptr_ok_def] >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  `i.inst_opcode <> PHI` by
    (strip_tac >> qpat_x_assum `step_inst_base i s = OK post` mp_tac >>
     simp[step_inst_base_def]) >>
  Cases_on `MEM i.inst_opcode [MLOAD; MCOPY; ILOAD; ISTORE; CALLDATALOAD; CALLDATASIZE;
      CALLDATACOPY; CODECOPY; EXTCODECOPY; RETURNDATACOPY; DLOADBYTES; SHA3; LOG]`
  >- (drule_all layout_canonical_memory_success >> simp[]) >>
  Cases_on `MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2]`
  >- (drule_all layout_canonical_external_success >> simp[]) >>
  drule_all layout_base_opcode_cases >> disch_tac >>
  drule_all layout_canonical_ordinary_nonterm_success >> simp[]
QED

Theorem layout_canonical_base_jump:
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
    q n i s j t a /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode <> INVOKE /\
  is_terminator i.inst_opcode /\ step_inst_base i s = OK post ==>
  ?g tpost. a = INL g /\ step_inst_base j t = OK tpost /\
    layout_completed_jump D lo vs0 C C' q0 es qs qend g i j s t post tpost /\
    control_agree post tpost
Proof
  strip_tac >> Cases_on `a`
  >- (drule_all layout_canonical_jump_success >> metis_tac[]) >>
  drule_all layout_canonical_corridor_success >> simp[]
QED

Theorem layout_canonical_base_exit:
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
    q n i s j t a /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode <> INVOKE /\
  step_inst_base i s = r /\ (!p. r <> OK p) /\ (!e. r <> Error e) ==>
  ?r'. step_inst_base j t = r' /\
    layout_canonical_result D lo vs0 C C' q0 es qs ass qend q n r r'
Proof
  strip_tac >> Cases_on `a`
  >- (Cases_on `is_terminator i.inst_opcode`
      >- (drule_all layout_canonical_terminal_exit >> simp[]) >>
      drule_all layout_canonical_abort_exit >> simp[]) >>
  drule_all layout_canonical_corridor_exit >> simp[]
QED

(* The certificate's es and qs are the path's projections. *)
val on_path = REWRITE_RULE [] o
  Q.INST [`es` |-> `MAP FST path`, `qs` |-> `MAP SND path`];

Theorem layout_canonical_base_certificate:
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
  fixed_region_reserved lo C /\ activation_depth q0 = 0 ==>
  selected_base_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
Proof
  strip_tac >>
  qpat_x_assum `es = _` SUBST_ALL_TAC >> qpat_x_assum `qs = _` SUBST_ALL_TAC >>
  rewrite_tac[selected_base_certificate_def, selected_step_match_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `layout_canonical_ES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [layout_canonical_ES_def]) >>
  `j.inst_opcode <> INVOKE` by metis_tac[layout_canonical_step_witness_not_invoke] >>
  simp[layout_deferred_noninvoke] >>
  Cases_on `?p. r = OK p`
  >- (qpat_x_assum `?p. _` strip_assume_tac >>
      qpat_x_assum `r = _` SUBST_ALL_TAC >> rename1 `OK post` >>
      Cases_on `is_terminator i.inst_opcode`
      >- (drule_all (on_path layout_canonical_base_jump) >> strip_tac >>
          qexists `OK tpost` >> conj_tac >- (irule finite_step_base >> simp[]) >>
          qpat_x_assum `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
          simp[layout_canonical_OS_def] >> rpt strip_tac >>
          drule_all (on_path layout_canonical_base_jump) >> strip_tac >> gvs[]) >>
      drule_all (on_path layout_canonical_base_nonterm_success) >> strip_tac >>
      qexists `OK tpost` >> conj_tac >- (irule finite_step_base >> simp[]) >>
      qpat_x_assum `layout_canonical_step_witness _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
      simp[layout_canonical_OS_def] >> rpt strip_tac >>
      drule_all (on_path layout_canonical_base_nonterm_success) >> strip_tac >> gvs[]) >>
  `!p. r <> OK p` by metis_tac[] >>
  drule_all (on_path layout_canonical_base_exit) >> strip_tac >>
  qexists `r'` >> conj_tac
  >- (irule finite_step_base >> simp[] >> metis_tac[layout_canonical_result_not_error]) >>
  simp[layout_canonical_OS_def] >> Cases_on `r` >> fs[]
QED
