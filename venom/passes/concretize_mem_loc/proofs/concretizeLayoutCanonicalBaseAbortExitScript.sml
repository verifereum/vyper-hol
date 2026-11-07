Theory concretizeLayoutCanonicalBaseAbortExit
Ancestors concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  ptrDiscipline venomExecSemantics venomInst list

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
  cheat
QED
