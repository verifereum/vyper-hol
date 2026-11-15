Theory concretizeLayoutRequestControl
Ancestors concretizeLayoutRequestCall concretizeLayoutRequestBlock
  concretizeLayoutRequestRun concretizeLayoutRequestRelations
  concretizeLayoutCanonicalDriver frameSelectedSimulation
  list

(* Structural half of the selected simulation contract.  The base opcode
   certificate is deliberately left to the simulation assembly consumer.
   The unchanged canonical run entry already carries request agreement;
   all instruction/block entries and result observations use the stronger
   request-aware relations. *)
Theorem layout_request_structural_certificates:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline lo C vs0 /\ vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_return_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend) /\
  selected_call_exit_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend) /\
  selected_term_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend) /\
  selected_next_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend) /\
  selected_block_exit_certificate C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend) /\
  selected_run_next_certificate C C' q0 path
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend) /\
  selected_run_halt_certificate C C' q0 path
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend) /\
  selected_run_exit_certificate C C' q0 path
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rpt conj_tac
  >- (irule layout_request_call_return_certificate >> metis_tac[])
  >- (irule layout_request_call_exit_certificate >> metis_tac[])
  >- simp[layout_request_term_certificate]
  >- (irule layout_request_next_certificate >> metis_tac[])
  >- simp[layout_request_block_exit_certificate]
  >- (irule layout_request_run_next_certificate >> metis_tac[])
  >- (irule layout_request_run_halt_certificate >> metis_tac[])
  >> irule layout_request_run_exit_certificate >> metis_tac[]
QED

val _ = export_theory();
