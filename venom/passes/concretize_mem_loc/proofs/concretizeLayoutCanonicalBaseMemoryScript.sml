Theory concretizeLayoutCanonicalBaseMemory
Ancestors concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  ptrDiscipline venomExecSemantics venomInst list
  concretizeLayoutExceptionalEntry concretizeLayoutExceptionalCopy
  concretizeLayoutRankedCorridor concretizeLayoutPhaseCorridor
  concretizeLayoutBlockPairing concretizeStepStructure contextCodegenRel arithmetic
  frameFiniteJointDecoration frameJointTrace concretizeLayoutPhaseOrigin
  frameRelocationEnvironment frameRelocationLocal concretizeLayoutEntryFlags

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
  cheat
QED
