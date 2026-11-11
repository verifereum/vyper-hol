Theory concretizeLayoutCanonicalContract
Ancestors concretizeLayoutCanonicalBaseCertificate concretizeLayoutCanonicalBlock
  concretizeLayoutCanonicalCallReturn concretizeLayoutCanonicalDeferredExit
  concretizeLayoutCanonicalRunNext concretizeLayoutCanonicalRunHalt
  concretizeLayoutCanonicalRunExit frameSelectedSimulation

(* The nine certificates of the selected simulation contract for the
   canonical layout relations, with the deferred step outcome. *)
Theorem layout_canonical_simulation_contract:
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
  joint_trace vs0 C q0 es qs qend ==>
  selected_simulation_contract C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_simulation_contract_def] >>
  rpt conj_tac
  >- (irule layout_canonical_base_certificate >> metis_tac[])
  >- (irule layout_canonical_call_return_certificate >> metis_tac[])
  >- (irule layout_deferred_call_exit_certificate >> metis_tac[])
  >- simp[layout_canonical_term_certificate]
  >- (irule layout_canonical_next_certificate >> metis_tac[])
  >- simp[layout_canonical_block_exit_certificate]
  >- (irule layout_canonical_run_next_certificate >> metis_tac[])
  >- (irule layout_canonical_run_halt_certificate >> metis_tac[])
  >> irule layout_canonical_run_exit_certificate >> metis_tac[]
QED

val _ = export_theory();
