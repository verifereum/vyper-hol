Theory concretizeLayoutCanonicalBaseJump
Ancestors concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  concretizeLayoutCompletedConditionalJump concretizeLayoutAlignedControl
  concretizeStepStructure concretizeLayoutBlockPairing concretizeLayoutEntryFlags
  ptrDiscipline venomExecSemantics venomInst list

(* Leaf of the exhaustive base certificate: a terminator that steps to OK
   (JMP, JNZ, DJMP) completes the jump, as layout_canonical_OS requires. *)

Theorem layout_canonical_jump_success:
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
  is_terminator i.inst_opcode /\ step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_completed_jump D lo vs0 C C' q0 es qs qend g i j s t post tpost /\
    control_agree post tpost
Proof
  strip_tac >>
  `MEM i.inst_opcode [JMP; JNZ; DJMP]` by
    (Cases_on `i.inst_opcode` >> gvs[is_terminator_def] >>
     qpat_x_assum `step_inst_base i s = OK post` mp_tac >>
     pure_once_rewrite_tac[step_inst_base_def] >>
     asm_rewrite_tac[opcode_case_def] >>
     simp[AllCaseEqs()] >> rpt strip_tac >>
     pairarg_tac >> gvs[]) >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `i.inst_opcode <> ALLOCA /\ i.inst_opcode <> NOP` by
    gvs[MEM] >>
  `j = i` by gvs[concretize_positions_unchanged] >>
  qpat_x_assum `j = i` SUBST_ALL_TAC >>
  `get_instruction g.lop_origin.lbo_target t.vs_inst_idx = SOME i` by
    (drule_all layout_block_pair_lookup >>
     simp[concretize_positions_unchanged]) >>
  `~vs0.vs_halted` by
    fs[o1PassContractTheory.o1_run_state_ok_def,
       unitTransformDefsTheory.o1_initial_state_ok_def] >>
  `?tpost. layout_completed_jump D lo vs0 C C' q0 es qs qend
      g i i s t post tpost` by
    (Cases_on `i.inst_opcode = JMP`
     >- (drule_all layout_ordinary_entry_nonhalting >> strip_tac >>
         drule_all layout_completed_jmp >> simp[]) >>
     irule layout_completed_conditional_jump >> simp[MEM] >>
     metis_tac[MEM]) >>
  qexists `tpost` >>
  `control_agree s t` by fs[layout_aligned_entry_def] >>
  drule_all layout_aligned_jump_state >>
  simp[layout_aligned_state_def] >> strip_tac >>
  fs[layout_completed_jump_def]
QED
