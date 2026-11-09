Theory concretizeLayoutCanonicalCallEntry
Ancestors concretizeLayoutCanonicalDriver concretizeLayoutCallRunEntry
  concretizeLayoutPairedEntry concretizeLayoutAlignedControl
  concretizeLayoutPhaseCorridor concretizeLayoutPhaseOrigin
  frameRankedTerminalCorridor concretizeStepStructure
  frameSelectedSimulation frameFiniteJointDecoration frameSelectedDecoration frameFiniteExecution
  frameJointTrace frameJointTransition frameOriginHistory frameOriginReachable
  frameAllocationOwnership contextCodegenRel frameRelocationEnvironment
  concretizeLayoutStagePairing concretizeLayoutCanonicalIndex concretizeMemLocDefs
  ptrDiscipline o1PassContract venomWf venomInstProofs1 venomExecProofs
  frameControlAgreement frameResolvedCoherent frameActivationLifetime
  venomInst list arithmetic

Theorem layout_canonical_invoke_witness:
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t /\
  i.inst_opcode = INVOKE ==>
  j = i /\ ?a. layout_driver_indexed es ass a /\
    ~a.lop_pending /\ a.lop_config = q /\ a.lop_cursor = n /\
    layout_aligned_entry D lo vs0 C C' q0 es qs qend a s t
Proof
  simp[layout_canonical_ES_def, layout_canonical_step_witness_def] >>
  strip_tac >> Cases_on `a`
  >- (gvs[layout_canonical_block_witness_def, layout_paired_ordinary_def,
          concretize_positions_unchanged] >> metis_tac[]) >>
  gvs[layout_canonical_block_witness_def, layout_corridor_entry_def,
      ranked_terminal_entry_def, layout_phase_normalize_def] >>
  Cases_on `y.ltp_remaining`
  >- gvs[ranked_terminal_corridor_def] >>
  fs[ranked_terminal_corridor_def] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem lookup_function_fn_name[local]:
  !name fns fn. lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct_on `fns` >> rw[lookup_function_def, FIND_thm]
QED

Theorem layout_canonical_call_entry:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ptr_discipline lo C vs0 /\ vs0.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  joint_trace vs0 C q0 es qs qend /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  decoration_at caller i s q /\ i.inst_opcode = INVOKE /\
  decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
  joint_transition C q NONE qc /\ joint_segment C qc wc qe /\
  selected_segment C q0 path n q ((NONE,qc)::wc) qe /\
  layout_canonical_ES D lo vs0 C C' q0 path es qs ass qend q n i s j t ==>
  j = i /\ ?out ct phase.
    lookup_function name C'.ctx_functions = SOME out /\
    (?args'. eval_operands ops t = SOME args' /\ setup_callee out args' t = SOME ct) /\
    layout_canonical_run D lo vs0 C C' q0 es qs ass qend qc (n+1) fn cs out ct /\
    layout_driver_indexed es ass phase /\ ~phase.lop_pending /\
    phase.lop_config = q /\ phase.lop_cursor = n /\
    layout_ordinary_entry D lo vs0 C C' q0 es qs qend phase s t /\ control_agree s t
Proof
  strip_tac >>
  drule_all layout_canonical_invoke_witness >> strip_tac >> gvs[] >>
  rename1 `layout_driver_indexed _ _ phase` >>
  Cases_on `phase.lop_config` >>
  gvs[decoration_at_def] >>
  rename1 `phase.lop_config = JointConfig stk PG G tn caller i s oms om hs hist` >>
  `layout_ordinary_entry D lo vs0 C C' q0 (MAP FST path) (MAP SND path)
      qend phase s t /\ control_agree s t` by fs[layout_aligned_entry_def] >>
  `phase.lop_ids = EL phase.lop_cursor (lifetime_annotations 0 [0] (MAP FST path)) /\
   phase.lop_anns = EL phase.lop_cursor ass` by
    fs[layout_driver_indexed_def, layout_phase_canonical_def] >>
  `selected_segment C q0 path phase.lop_cursor phase.lop_config [(NONE,qc)] qc` by
    (irule (cj 1 selected_segment_parts) >>
     conj_tac >- gvs[joint_segment_def] >>
     qexistsl [`qe`, `wc`] >> gvs[joint_segment_def]) >>
  drule selected_singleton_event >> strip_tac >>
  drule selected_segment_indices >> strip_tac >>
  `phase.lop_cursor < LENGTH path` by fs[] >>
  `qc = EL (SUC phase.lop_cursor) (q0::MAP SND path)` by gvs[GSYM ADD1] >>
  `resolved_annotation_edge C phase.lop_cursor phase.lop_config NONE qc
    phase.lop_ids phase.lop_anns
    (EL (SUC phase.lop_cursor) (lifetime_annotations 0 [0] (MAP FST path)))
    (EL (SUC phase.lop_cursor) ass)` by
    (qpat_x_assum `!k. _ ==> resolved_annotation_edge _ _ _ _ _ _ _ _ _`
       (qspec_then `phase.lop_cursor` mp_tac) >>
     fs[EL_MAP] >> gvs[]) >>
  `joint_config_reachable vs0 C phase.lop_config` by
    (drule joint_trace_prefix_reachable >>
     pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `phase.lop_cursor` mp_tac) >> gvs[]) >>
  `frame_reachable vs0 C stk PG G tn caller i s` by
    (qpat_x_assum `joint_config_reachable _ _ _` mp_tac >>
     asm_rewrite_tac[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `MEM caller C.ctx_functions` by metis_tac[frame_allocation_ownership] >>
  `o1_fn_shape C caller /\ o1_fn_shape C fn /\ fn.fn_eom = NONE` by
    (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  `?P. fn_ptr_ok P caller` by
    (fs[ptr_discipline_def, EVERY_MEM] >> metis_tac[]) >>
  `taint_ok caller tn i s` by (fs[ptr_discipline_def] >> metis_tac[]) >>
  `MEM i (fn_insts caller)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  drule_all layout_stage_row_produce >> strip_tac >>
  `out.fn_blocks = (concretize_function_with_positions layout.cl_positions fn).fn_blocks` by
    fs[layout_stage_row_def, apply_context_concretize_layout_def, apply_concretize_layout_def] >>
  `EVERY bb_well_formed fn.fn_blocks /\ ~NULL out.fn_blocks` by
    (fs[o1_fn_shape_def, wf_function_def, EVERY_MEM,
        fn_has_entry_def, concretize_positions_blocks, NULL_EQ]) >>
  `s.vs_labels = t.vs_labels` by
    (qpat_x_assum `phase.lop_config = _` (fn th =>
       fs[layout_ordinary_entry_def, layout_ordinary_state_def, th, relocation_env_def])) >>
  `?birth ids rp rv anns. phase.lop_ids = birth::ids /\ phase.lop_anns = (rp,rv)::anns` by
    (qpat_x_assum `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[layout_ordinary_entry_def, layout_ordinary_state_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  `phase.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  `MEM fn C.ctx_functions /\ layout_driver_row C' fn out layout.cl_positions` by
    (simp[layout_driver_row_def] >>
     metis_tac[lookup_function_MEM, lookup_function_fn_name]) >>
  gvs[] >>
  drule layout_selected_call_scoped_run >> simp[] >>
  qpat_x_assum `birth::ids = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `(rp,rv)::anns = _` (SUBST_ALL_TAC o SYM) >>
  simp[NoAsms] >>
  `~NULL out.fn_blocks` by simp[] >>
  disch_then (qspec_then `INL phase` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  qexistsl [`ct`, `phase`] >> simp[GSYM ADD1] >>
  first_x_assum irule >> simp[]
QED

val _ = export_theory();
