(* The prefix certificates of the selected simulation for the canonical
   layout relations: the entry halves of the next and run-next
   certificates, a run's entry, a call's entry, and the instruction a
   prefix ends on. *)
Theory concretizeLayoutCanonicalPrefix
Ancestors concretizeLayoutCanonicalContract concretizeLayoutCanonicalRunNext
  concretizeLayoutCanonicalCallEntry concretizeLayoutCanonicalBlock
  concretizeLayoutCanonicalDriver concretizeLayoutSelectedBaseInterface
  concretizeStepStructure frameSelectedPrefix frameSelectedSimulation
  frameSelectedDecoration frameFiniteJointDecoration

Theorem layout_canonical_run_entry_certificate:
  EVERY wf_function C.ctx_functions ==>
  selected_run_entry_certificate C C' q0 path
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
Proof
  rewrite_tac[selected_run_entry_certificate_def] >> rpt strip_tac
  >- metis_tac[layout_canonical_run_fn_name] >>
  drule_all layout_canonical_run_block_entry >> strip_tac >>
  qexistsl [`bb'`, `phi' with vs_inst_idx := phi_prefix_length bb'.bb_instructions`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[target_block_entry_def] >> metis_tac[]
QED

Theorem layout_canonical_call_entry_certificate:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  layout_cut_safe D lo ncut vs0 C qend /\ vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) ==>
  selected_call_entry_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
Proof
  strip_tac >> rewrite_tac[selected_call_entry_certificate_def] >>
  rpt strip_tac >>
  `joint_segment C qc [] qc` by simp[joint_segment_def] >>
  drule_all layout_canonical_call_entry >> strip_tac >>
  qexistsl [`name`, `ops`, `out`, `args'`, `ct`] >> gvs[]
QED

Theorem layout_canonical_prefix_end_certificate:
  selected_prefix_end_certificate C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
Proof
  rewrite_tac[selected_prefix_end_certificate_def, layout_canonical_EB_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?a. _` strip_assume_tac >>
  `i.inst_opcode <> NOP` by (strip_tac >> gvs[]) >>
  drule_all layout_canonical_block_witness_step >> strip_tac >>
  `get_instruction bb' t.vs_inst_idx = SOME j` by metis_tac[] >>
  qexists `j` >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (strip_tac >> `j = i` suffices_by simp[] >>
      Cases_on `a`
      >- gvs[layout_canonical_step_witness_def, concretize_positions_unchanged] >>
      gvs[layout_canonical_block_witness_def] >>
      drule_all layout_canonical_corridor_instruction >> gvs[]) >>
  strip_tac >> simp[layout_canonical_ES_def, layout_base_lookahead_def] >>
  metis_tac[]
QED

(* The five prefix certificates, under the premises of the simulation
   contract. *)
Theorem layout_canonical_prefix_certificates:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  layout_cut_safe D lo ncut vs0 C qend /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  dead_wf D /\ es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  callee_first names C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_defs_reach_uses C.ctx_functions /\ EVERY all_reachable C.ctx_functions /\
  fixed_region_reserved lo C /\ activation_depth q0 = 0 /\
  joint_trace vs0 C q0 es qs qend ==>
  selected_prefix_certificates C C' q0 path
    (layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend)
    (layout_canonical_EB D lo vs0 C C' q0 es qs ass qend)
    (layout_canonical_run D lo vs0 C C' q0 es qs ass qend)
    (events_OS C C' (layout_deferred_OS D lo vs0 C C' q0 path es qs ass qend))
    (events_OB C C' (layout_canonical_OB D lo vs0 C C' q0 es qs ass qend))
    (events_OutR C C' (layout_canonical_OutR D lo vs0 C C' q0 es qs ass qend))
Proof
  strip_tac >> rewrite_tac[selected_prefix_certificates_def] >>
  rpt conj_tac
  >- (irule layout_canonical_next_entry_certificate >> metis_tac[])
  >- (irule layout_canonical_run_next_entry_certificate >> metis_tac[])
  >- (irule layout_canonical_run_entry_certificate >> simp[])
  >- (irule layout_canonical_call_entry_certificate >> metis_tac[])
  >> simp[layout_canonical_prefix_end_certificate]
QED

val _ = export_theory();
