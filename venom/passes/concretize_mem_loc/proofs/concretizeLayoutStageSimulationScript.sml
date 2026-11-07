Theory concretizeLayoutStageSimulation
Ancestors concretizeLayoutCanonicalContract concretizeLayoutStageEntry
  frameSelectedSimulation frameDecorationComplete frameResolvedCoherent
  frameFiniteJointDecoration frameJointTrace frameSelectedDecoration list

(* The generic selected driver is the only recursive simulation used here. *)
Theorem layout_stage_selected_run:
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
    layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend
      q n qe (n + LENGTH w) fn s fn' t r r'
Proof
  strip_tac >>
  `selected_simulation_contract C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend)` by
    (irule layout_canonical_simulation_contract >> metis_tac[]) >>
  drule_all selected_run_simulation >> simp[selected_run_match_def]
QED

Theorem layout_segment_chain[local]:
  !w q qe. joint_segment C q w qe ==>
    joint_chain C q (MAP FST w) (MAP SND w) qe
Proof
  Induct >> simp[joint_segment_def, joint_chain_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[joint_segment_def, joint_chain_def] >> metis_tac[]
QED

(* One ambient source decoration and one coherent annotation sequence. *)
Theorem layout_stage_source_decoration:
  finite_run C fn s r /\ enters_block fn s p /\
  joint_initial vs0 C q0 /\ decoration_entry fn p q0 /\
  ALL_DISTINCT (fn_labels fn) /\
  EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions /\
  ~ctx_has_dalloca C ==>
  ?path qe d ass.
    decorated_run C fn s r q0 0 path qe d /\
    selected_segment C q0 path 0 q0 path qe /\
    joint_trace vs0 C q0 (MAP FST path) (MAP SND path) qe /\
    EL 0 ass = [([],FEMPTY)] /\
    (!k. k < LENGTH path ==>
      resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
        (EL (SUC k) (q0::MAP SND path))
        (EL k (lifetime_annotations 0 [0] (MAP FST path))) (EL k ass)
        (EL (SUC k) (lifetime_annotations 0 [0] (MAP FST path)))
        (EL (SUC k) ass))
Proof
  strip_tac >> drule (cj 3 finite_decoration_complete) >>
  disch_then (qspecl_then [`q0`, `0`, `p`] mp_tac) >>
  simp[] >> strip_tac >>
  `joint_segment C q0 w qe` by metis_tac[cj 3 decorated_execution_segment] >>
  `joint_trace vs0 C q0 (MAP FST w) (MAP SND w) qe` by
    (simp[joint_trace_def] >> metis_tac[layout_segment_chain]) >>
  drule_all joint_trace_coherent_annotations >> strip_tac >>
  qexistsl [`w`, `qe`, `d`, `ass`] >> simp[] >>
  simp[selected_segment_def, joint_segment_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >>
  simp[EL_MAP]
QED

val _ = export_theory();
