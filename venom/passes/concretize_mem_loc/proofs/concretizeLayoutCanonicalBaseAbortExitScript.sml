Theory concretizeLayoutCanonicalBaseAbortExit
Ancestors concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  ptrDiscipline venomExecSemantics venomInst list opcodeClass
  concretizeLayoutPhaseAbort concretizeLayoutExternalAbort
  concretizeStepStructure passSharedFrame

(* Leaf of the exhaustive base certificate: a non-terminator that halts or
   aborts (failed assertions, external aborts, static-context writes). *)

Theorem layout_canonical_abort_exit:
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
  ~is_terminator i.inst_opcode /\
  step_inst_base i s = r /\ (!p. r <> OK p) /\ (!e. r <> Error e) ==>
  ?r'. step_inst_base j t = r' /\
    layout_canonical_result D lo vs0 C C' q0 es qs ass qend q n r r'
Proof
  strip_tac >> Cases_on `r` >> gvs[]
  >- (drule step_inst_base_halt_opcodes >> strip_tac >>
      gvs[is_terminator_def])
  >- (drule_all layout_canonical_ordinary_environment >> strip_tac >>
      drule step_inst_base_abort_opcode >> simp[] >> strip_tac >>
      gvs[concretize_positions_unchanged] >>
      (Cases_on `i.inst_opcode = RETURNDATACOPY`
      >- (gvs[] >>
          `?opd ops opn dst src sz.
             i.inst_operands = [opd;ops;opn] /\
             eval_operand opd s = SOME dst /\
             eval_operand ops s = SOME src /\
             eval_operand opn s = SOME sz` by
            (qpat_x_assum `step_inst_base i s = Abort a v` mp_tac >>
             simp[Once step_inst_base_def] >>
             simp[AllCaseEqs()] >> metis_tac[]) >>
          drule_all layout_returncopy_abort_step >>
          disch_then (qspecl_then [`ARB`, `ARB`] strip_assume_tac) >>
          simp[layout_canonical_result_def]) >> gvs[] >>
      `?tpost. step_inst_base i t = Abort a tpost /\
         dead_result_rel D (Abort a v) (Abort a tpost)` by
        (FIRST
          [`MEM i.inst_opcode [ASSERT; ASSERT_UNREACHABLE; SELFDESTRUCT]` by simp[] >>
             drule_all layout_guard_abort_step,
           `MEM i.inst_opcode [CALL; CREATE; CREATE2]` by simp[] >>
             drule_all layout_external_abort_step,
           `MEM i.inst_opcode [INVALID; REVERT; SSTORE; TSTORE; LOG]` by simp[] >>
             drule_all layout_simple_abort_step] >> metis_tac[]) >>
      simp[layout_canonical_result_def])) >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[is_terminator_def]
QED
