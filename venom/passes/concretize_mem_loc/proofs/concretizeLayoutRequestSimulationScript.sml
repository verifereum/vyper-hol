Theory concretizeLayoutRequestSimulation
Ancestors concretizeLayoutRequestBase concretizeLayoutRequestControl
  concretizeLayoutCorridorRequests concretizeLayoutStageSimulation
  passSharedFrame frameSelectedSimulation concretizeLayoutRequestRelations
  concretizeLayoutCanonicalDriver list

(* Assemble the strengthened observations without changing the canonical
   recursive driver or its run-entry relation. *)
Theorem layout_request_simulation_contract:
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
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_simulation_contract_def] >>
  conj_tac
  >- (irule layout_request_base_certificate >>
      metis_tac[step_inst_base_abort_requests]) >>
  irule layout_request_structural_certificates >> metis_tac[]
QED

(* Use precisely the same decoration, selected segment, and initialization
   as layout_stage_selected_run, retaining the request observation. *)
Theorem layout_stage_request_selected_run:
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
  joint_trace vs0 C q0 es qs qend /\
  decorated_run C fn s r q n w qe d /\
  selected_segment C q0 path n q w qe /\
  layout_canonical_run D lo vs0 C C' q0 es qs ass qend q n fn s fn' t ==>
  ?r'. finite_run C' fn' t r' /\
    layout_request_OutR D lo vs0 C C' q0 es qs ass qend
      q n qe (n + LENGTH w) fn s fn' t r r'
Proof
  strip_tac >>
  `selected_simulation_contract C C' q0 path
    (layout_request_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_request_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_request_OutR D lo vs0 C C' q0 es qs ass qend)` by
    (irule layout_request_simulation_contract >> metis_tac[]) >>
  drule_all selected_run_simulation >> simp[selected_run_match_def]
QED

(* Constructor compatibility comes from the old canonical result; the new
   guard supplies the observation that its Abort branch deliberately omits. *)
Theorem layout_request_OutR_abort:
  layout_request_OutR D lo vs0 C C' q0 es qs ass qend
    q n qe m fn s fn' t (Abort a post) r' ==>
  ?b post'. r' = Abort b post' /\
    LIST_REL (request_agree_except D) post.vs_requests post'.vs_requests
Proof
  simp[layout_request_OutR_def, layout_canonical_OutR_def] >>
  strip_tac >> Cases_on `r'` >>
  gvs[layout_canonical_result_def, layout_request_guard_def,
      layout_request_state_def]
QED

val _ = export_theory();
