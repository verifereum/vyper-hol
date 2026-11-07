Theory concretizeLayoutCanonicalBase
Ancestors concretizeLayoutCanonicalDriver concretizeLayoutCanonicalIndex frameResolvedCoherent
  concretizeLayoutPhaseSuccess concretizeLayoutEntryFlags
  concretizeLayoutPhaseOrigin concretizeLayoutAlignedControl venomExecSemantics
  frameFiniteJointDecoration frameJointTrace frameOriginHistory frameOriginReachable
  frameAllocationOwnership frameJointTransition contextCodegenRel
  o1PassContract ptrDiscipline venomInst concretizeLayoutPhaseNop
  concretizeStepStructure concretizeLayoutSelectedBaseInterface list
  concretizeLayoutPhaseAssign venomWf concretizeLayoutPhaseValues
  concretizeLayoutPhaseAllocation concretizeLayoutStagePairing
  concretizeMemLocDefs passSharedDefs
  concretizeLayoutPhaseShift concretizeLayoutPhaseOffset
  concretizeLayoutPhaseEnvironment concretizeLayoutPhaseContext
  concretizeLayoutReaderContext concretizeLayoutPhaseStorage
  concretizeLayoutPhaseIndexedContext concretizeLayoutLocalIndexedContextReaders
  frameRelocationCleanValueSteps frameRelocationScalarSteps concretizeLayoutPhaseAffine concretizeLayoutPhaseCompare

Theorem layout_annotation_update_ordinary_unique:
  ev = SOME (OriginOrdinary fuel post) /\
  resolved_annotation_update q ev ids anns left /\
  resolved_annotation_update q ev ids anns right ==>
  left = right
Proof
  Cases_on `q` >> simp[Once resolved_annotation_update_cases] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `resolved_annotation_update _ _ _ _ _` mp_tac >>
  simp[Once resolved_annotation_update_cases] >> rpt strip_tac >> gvs[]
QED

Theorem layout_driver_indexed_ordinary:
  layout_driver_indexed es ass g /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  k.lop_cursor = SUC g.lop_cursor /\ k.lop_ids = g.lop_ids /\
  resolved_annotation_update g.lop_config (EL g.lop_cursor es)
    g.lop_ids g.lop_anns k.lop_anns /\
  resolved_annotation_edge C g.lop_cursor g.lop_config (EL g.lop_cursor es) q'
    g.lop_ids (EL g.lop_cursor ass) ids' (EL (SUC g.lop_cursor) ass) ==>
  layout_driver_indexed es ass k
Proof
  simp[layout_driver_indexed_def, resolved_annotation_edge_def] >> strip_tac >>
  conj_tac
  >- (irule layout_phase_canonical_ordinary >> goal_assum (drule_at Any) >> simp[]) >>
  irule layout_annotation_update_ordinary_unique >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem layout_canonical_ordinary_success:
  layout_aligned_entry D lo vs0 C C' q0 es qs qend g s t /\
  layout_driver_indexed es ass g /\ g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
  k.lop_ids = g.lop_ids /\
  resolved_annotation_update g.lop_config (EL g.lop_cursor es)
    g.lop_ids g.lop_anns k.lop_anns /\
  resolved_annotation_edge C g.lop_cursor g.lop_config (EL g.lop_cursor es) q'
    g.lop_ids (EL g.lop_cursor ass) ids' (EL (SUC g.lop_cursor) ass) /\
  layout_phase_ok_abort D lo vs0 C C' q0 es qs qend
    (INL g) (INL k) (OK post) (OK tpost) /\
  step_inst fuel C i s = OK post /\ step_inst_base j t = OK tpost /\
  j.inst_opcode <> INVOKE /\
  ~is_terminator i.inst_opcode /\ ~is_terminator j.inst_opcode ==>
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend
    g.lop_cursor F (INL g) post tpost
Proof
  strip_tac >>
  `layout_driver_indexed es ass k` by
    (irule layout_driver_indexed_ordinary >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `layout_ordinary_entry D lo vs0 C C' q0 es qs qend k post tpost /\
   k.lop_origin = g.lop_origin` by
    gvs[layout_phase_ok_abort_def, layout_phase_entry_def, layout_phase_origin_def] >>
  `step_inst 0 C' j t = OK tpost` by simp[step_inst_non_invoke] >>
  `layout_aligned_entry D lo vs0 C C' q0 es qs qend k post tpost` by
    (irule layout_aligned_step >> goal_assum (drule_at Any) >> metis_tac[]) >>
  simp[layout_canonical_success_def] >> qexists_tac `INL k` >>
  simp[layout_phase_origin_def] >>
  metis_tac[layout_ordinary_entry_halted_agree]
QED

Theorem layout_driver_annotation_edge_at:
  layout_driver_indexed (MAP FST path) ass g /\
  layout_ordinary_trace vs0 C q0 (MAP FST path) (MAP SND path) qend g s /\
  g.lop_cursor < LENGTH path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] (MAP FST path))) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] (MAP FST path))) (EL (SUC k) ass)) ==>
  resolved_annotation_edge C g.lop_cursor g.lop_config (EL g.lop_cursor (MAP FST path))
    (EL (SUC g.lop_cursor) (q0::MAP SND path)) g.lop_ids g.lop_anns
    (EL (SUC g.lop_cursor) (lifetime_annotations 0 [0] (MAP FST path)))
    (EL (SUC g.lop_cursor) ass)
Proof
  strip_tac >>
  qpat_x_assum `!k. _ ==> resolved_annotation_edge _ _ _ _ _ _ _ _ _`
    (qspec_then `g.lop_cursor` mp_tac) >>
  gvs[layout_driver_indexed_def, layout_phase_canonical_def,
    layout_ordinary_trace_def, EL_MAP]
QED

Theorem layout_canonical_ordinary_step_witness:
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) ==>
  ~g.lop_pending /\ g.lop_config = q /\ g.lop_cursor = n /\
  layout_driver_indexed es ass g /\
  layout_aligned_entry D lo vs0 C C' q0 es qs qend g s t /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME i /\
  ?fn fn' positions. decoration_entry fn s q /\
    layout_driver_row C' fn fn' positions /\
    layout_block_pair positions g.lop_origin.lbo_source g.lop_origin.lbo_target
      s.vs_inst_idx t.vs_inst_idx /\
    ((i.inst_opcode = NOP /\ j = i) \/
     ((concretize_inst_with_positions positions i).inst_opcode <> NOP /\
      j = concretize_inst_with_positions positions i))
Proof
  simp[layout_canonical_step_witness_def, layout_canonical_block_witness_def,
    concretizeLayoutPairedEntryTheory.layout_paired_ordinary_def] >>
  metis_tac[]
QED

Theorem layout_ordinary_source_facts:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs qend g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  decoration_at fn inst s g.lop_config ==>
  frame_reachable vs0 C stk PG G tn fn inst s /\
  MEM fn C.ctx_functions /\ o1_fn_shape C fn /\ MEM inst (fn_insts fn) /\
  access_ok lo G fn inst s /\ taint_ok fn tn inst s
Proof
  strip_tac >>
  `joint_config_reachable vs0 C g.lop_config` by
    (fs[layout_ordinary_entry_def, layout_ordinary_trace_def] >>
     drule joint_trace_prefix_reachable >> pure_rewrite_tac[EVERY_EL] >>
     disch_then (qspec_then `g.lop_cursor` mp_tac) >> gvs[]) >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (gvs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `MEM fn C.ctx_functions` by metis_tac[frame_allocation_ownership] >>
  `o1_fn_shape C fn` by (fs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM inst (fn_insts fn)` by
    (qpat_x_assum `decoration_at _ _ _ _` mp_tac >>
     simp[decoration_at_def, active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  fs[ptr_discipline_def] >> metis_tac[]
QED

Theorem layout_canonical_ordinary_environment:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\ decoration_at fn i s q ==>
  ~g.lop_pending /\ g.lop_config = q /\ g.lop_cursor = n /\
  layout_driver_indexed es ass g /\
  layout_aligned_entry D lo vs0 C C' q0 es qs qend g s t /\
  layout_ordinary_entry D lo vs0 C C' q0 es qs qend g s t /\
  layout_ordinary_trace vs0 C q0 es qs qend g s /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME i /\
  MEM fn C.ctx_functions /\ o1_fn_shape C fn /\ MEM i (fn_insts fn) /\
  fn_ptr_ok P fn /\
  ?stk PG G tn oms om hs h birth ids rp rv anns f f' positions.
    q = JointConfig stk PG G tn fn i s oms om hs h /\
    g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
    frame_reachable vs0 C stk PG G tn fn i s /\
    access_ok lo G fn i s /\ taint_ok fn tn i s /\
    decoration_entry f s q /\ layout_driver_row C' f f' positions /\
    layout_block_pair positions g.lop_origin.lbo_source g.lop_origin.lbo_target
      s.vs_inst_idx t.vs_inst_idx /\
    ((i.inst_opcode = NOP /\ j = i) \/
     ((concretize_inst_with_positions positions i).inst_opcode <> NOP /\
      j = concretize_inst_with_positions positions i))
Proof
  strip_tac >> drule layout_canonical_ordinary_step_witness >> strip_tac >>
  `layout_ordinary_entry D lo vs0 C C' q0 es qs qend g s t /\
   layout_ordinary_trace vs0 C q0 es qs qend g s` by
    fs[layout_aligned_entry_def, layout_ordinary_entry_def] >>
  Cases_on `q` >> gvs[decoration_at_def] >>
  `decoration_at fn i s g.lop_config` by simp[decoration_at_def] >>
  drule_all layout_ordinary_source_facts >> strip_tac >>
  `fn_ptr_ok P fn` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?birth ids rp rv anns. g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns` by
    (qpat_x_assum `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[layout_ordinary_entry_def, layout_ordinary_state_def] >>
     asm_rewrite_tac[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem layout_canonical_ordinary_edge:
  layout_driver_indexed (MAP FST path) ass g /\
  layout_ordinary_trace vs0 C q0 (MAP FST path) (MAP SND path) qend g s /\
  layout_base_lookahead C q0 path g.lop_config g.lop_cursor i s /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK post /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] (MAP FST path))) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] (MAP FST path))) (EL (SUC k) ass)) ==>
  g.lop_cursor < LENGTH (MAP FST path) /\
  g.lop_anns = EL g.lop_cursor ass /\
  ?fuel qn. EL g.lop_cursor (MAP FST path) = SOME (OriginOrdinary fuel post) /\
    EL (SUC g.lop_cursor) (q0::MAP SND path) = qn /\
    step_inst fuel C i s = OK post /\
    resolved_annotation_edge C g.lop_cursor g.lop_config
      (EL g.lop_cursor (MAP FST path)) qn g.lop_ids (EL g.lop_cursor ass)
      (EL (SUC g.lop_cursor) (lifetime_annotations 0 [0] (MAP FST path)))
      (EL (SUC g.lop_cursor) ass)
Proof
  strip_tac >> drule_all layout_base_lookahead_edge >> strip_tac >>
  drule layout_driver_annotation_edge_at >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  `step_inst fuel C i s = OK post` by simp[step_inst_non_invoke] >>
  fs[layout_driver_indexed_def] >> metis_tac[]
QED

Theorem layout_canonical_nop_success:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode = NOP /\ step_inst_base i s = OK post ==>
  step_inst_base j t = OK t /\
  layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post t
Proof
  strip_tac >> drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    simp[is_terminator_def] >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  drule_all layout_nop_trace_step >> strip_tac >>
  conj_tac >- simp[] >>
  drule layout_canonical_ordinary_success >>
  disch_then (qspecl_then [`t`, `EL g.lop_cursor (MAP SND path)`, `post`, `k`, `i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem layout_canonical_assign_success:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  i.inst_opcode = ASSIGN /\ step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >> drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    simp[is_terminator_def] >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  `inst_wf i` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?v. i.inst_outputs = [v]` by
    (qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  drule_all layout_assign_trace_step >> strip_tac >>
  qexists `tpost` >> conj_tac >- simp[] >>
  drule layout_canonical_ordinary_success >>
  disch_then (qspecl_then [`tpost`, `EL g.lop_cursor (MAP SND path)`, `post`, `k`, `i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem layout_canonical_clean_value_success:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  clean_value_shape i /\ ~MEM i.inst_opcode [ADD; SUB; EQ; LT; GT] /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >>
  `i.inst_opcode <> ALLOCA /\ i.inst_opcode <> INVOKE /\
   i.inst_opcode <> NOP /\ ~is_terminator i.inst_opcode` by
    (qpat_x_assum `clean_value_shape i` mp_tac >>
     simp[clean_value_shape_def, scalar_binary_opcode_def, MEM] >>
     rpt strip_tac >> gvs[is_terminator_def]) >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  `inst_wf i` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?v. i.inst_outputs = [v]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     qpat_x_assum `clean_value_shape i` mp_tac >>
     simp[clean_value_shape_def, scalar_binary_opcode_def, MEM] >>
     rpt strip_tac >> qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  `~MEM i.inst_opcode [ADD; SUB; EQ; LT; GT]` by simp[] >>
  drule_all layout_clean_value_trace_step >> strip_tac >>
  qexists `tpost` >> conj_tac >- simp[] >>
  drule layout_canonical_ordinary_success >>
  disch_then (qspecl_then [`tpost`, `EL g.lop_cursor (MAP SND path)`, `post`, `k`, `i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem layout_canonical_affine_success:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  (i.inst_opcode = ADD \/ i.inst_opcode = SUB) /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >>
  `i.inst_opcode <> ALLOCA /\ i.inst_opcode <> INVOKE /\
   i.inst_opcode <> NOP /\ ~is_terminator i.inst_opcode` by
    (gvs[is_terminator_def]) >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  `inst_wf i` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?v. i.inst_outputs = [v]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     Cases_on `i.inst_opcode = ADD` >> gvs[] >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_affine_trace_step >>
  disch_then (drule_at (Pat `g.lop_config = _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists `tpost` >> conj_tac >- simp[] >>
  drule layout_canonical_ordinary_success >>
  disch_then (qspecl_then [`tpost`, `EL g.lop_cursor (MAP SND path)`, `post`, `k`, `i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem layout_canonical_compare_success:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\ o1_ctx_shape C /\
  EVERY (\fn. fn.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ o1_run_state_ok vs0 /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs0 /\
  ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  MEM i.inst_opcode [EQ; LT; GT] /\ step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >>
  `i.inst_opcode <> ALLOCA /\ i.inst_opcode <> INVOKE /\
   i.inst_opcode <> NOP /\ ~is_terminator i.inst_opcode` by
    (fs[MEM, context_read0_opcode_def, clean_value_shape_def, scalar_binary_opcode_def] >>
     gvs[is_terminator_def]) >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by gvs[concretize_positions_unchanged] >> gvs[] >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  `inst_wf i` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?v. i.inst_outputs = [v]` by
    (qpat_x_assum `inst_wf i` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_compare_trace_step >>
  disch_then (drule_at (Pat `g.lop_config = _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  simp[] >>
  disch_then (qspecl_then [`rv`, `rpolicy`, `rp`, `anns`, `P`] mp_tac) >>
  simp[MEM] >> strip_tac >>
  qexists `tpost` >> conj_tac >- simp[] >>
  drule layout_canonical_ordinary_success >>
  disch_then (qspecl_then [`tpost`, `EL g.lop_cursor (MAP SND path)`, `post`, `k`, `i`] mp_tac) >>
  simp[] >> metis_tac[]
QED

(* Growing dispatch: validate the shared phase join before expanding families. *)
Theorem layout_canonical_ordinary_nonterm_success:
  o1_ctx_shape C /\ ptr_discipline lo C vs0 /\ ~ctx_has_dalloca C /\
  vs0.vs_allocas = FEMPTY /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  es = MAP FST path /\ qs = MAP SND path /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  layout_canonical_step_witness D lo vs0 C C' q0 es qs ass qend
    q n i s j t (INL g) /\
  layout_base_lookahead C q0 path q n i s /\ decoration_at fn i s q /\
  (MEM i.inst_opcode [NOP; ALLOCA; ASSIGN; ADD; SUB; SHL; SHR; SAR; OFFSET;
      CALLER; ADDRESS; CALLVALUE; GAS; SLOAD; TLOAD; BLOCKHASH; BLOBHASH; SSTORE; TSTORE] \/ context_read0_opcode i.inst_opcode \/
    (clean_value_shape i /\ ~MEM i.inst_opcode [ADD; SUB; EQ; LT; GT])) /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >>
  `i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode` by
    (fs[MEM, context_read0_opcode_def, clean_value_shape_def, scalar_binary_opcode_def] >>
     gvs[is_terminator_def]) >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  qpat_x_assum `es = _` SUBST_ALL_TAC >>
  qpat_x_assum `qs = _` SUBST_ALL_TAC >>
  qpat_x_assum `q = JointConfig _ _ _ _ _ _ _ _ _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `g.lop_cursor = n` (SUBST_ALL_TAC o SYM) >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >> simp[] >> strip_tac >>
  `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
  `inst_wf i` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `?k tpost. step_inst_base j t = OK tpost /\
    k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
    k.lop_ids = g.lop_ids /\
    resolved_annotation_update g.lop_config (EL g.lop_cursor (MAP FST path))
      g.lop_ids g.lop_anns k.lop_anns /\
    layout_phase_ok_abort D lo vs0 C C' q0 (MAP FST path) (MAP SND path) qend
      (INL g) (INL k) (OK post) (OK tpost)` by
    (Cases_on `i.inst_opcode = ALLOCA`
     >- (`f = fn` by gvs[decoration_entry_def, decoration_at_def] >> gvs[] >>
         rename1 `layout_driver_row C' fn fn' positions` >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         `?sz v. i.inst_operands = [Lit sz] /\ i.inst_outputs = [v]` by
           (qpat_x_assum `inst_wf i` mp_tac >>
            simp[inst_wf_def, LENGTH_EQ_NUM_compute, AllCaseEqs()] >> metis_tac[]) >>
         `FLOOKUP positions (Allocation i.inst_id) =
            SOME (concretize_positions C' fn i.inst_id)` by
           (qpat_x_assum `layout_driver_row _ _ _ _` mp_tac >>
            simp[layout_driver_row_def] >> strip_tac >> gvs[] >>
            drule_all layout_stage_row_position >> simp[]) >>
         drule_all layout_alloca_trace_step >> metis_tac[]) >>
     `j = i` by gvs[concretize_positions_unchanged] >>
     qpat_x_assum `j = i` SUBST_ALL_TAC >>
     `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
     `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
     Cases_on `i.inst_opcode = NOP`
     >- (gvs[] >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         drule_all layout_nop_trace_step >> metis_tac[]) >>
     Cases_on `MEM i.inst_opcode [SSTORE; TSTORE]`
     >- (gvs[] >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
           layout_state_write_trace_step >>
         disch_then (drule_at (Pat `g.lop_config = _`)) >>
         disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
         simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
         simp[] >> metis_tac[MEM]) >>
     `?v. i.inst_outputs = [v]` by
       (qpat_x_assum `inst_wf i` mp_tac >>
        fs[MEM, context_read0_opcode_def, clean_value_shape_def, scalar_binary_opcode_def] >>
        gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >> metis_tac[]) >>
     Cases_on `i.inst_opcode = ASSIGN`
     >- (gvs[] >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         drule_all layout_assign_trace_step >> metis_tac[]) >>
     Cases_on `MEM i.inst_opcode [ADD; SUB]`
     >- (`i.inst_opcode = ADD \/ i.inst_opcode = SUB` by metis_tac[MEM] >>
         drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
           layout_affine_trace_step >>
         disch_then (drule_at (Pat `g.lop_config = _`)) >>
         disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
         simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
         simp[] >> metis_tac[]) >>
     Cases_on `MEM i.inst_opcode [SHL; SHR; SAR]`
     >- (drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
           layout_shift_trace_step >>
         disch_then (drule_at (Pat `g.lop_config = _`)) >>
         disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
         simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
         simp[] >> metis_tac[]) >>
     Cases_on `i.inst_opcode = OFFSET`
     >- (`LENGTH i.inst_operands = 2` by
           (qpat_x_assum `inst_wf i` mp_tac >> simp[inst_wf_def] >>
            rpt strip_tac >> gvs[]) >>
         drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
           layout_offset_trace_step >>
         disch_then (drule_at (Pat `g.lop_config = _`)) >>
         disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
         simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
         simp[] >> metis_tac[]) >>
     Cases_on `MEM i.inst_opcode [CALLER; ADDRESS; CALLVALUE; GAS]`
     >- (gvs[] >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
           layout_environment_trace_step >>
         disch_then (drule_at (Pat `g.lop_config = _`)) >>
         disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
         simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`] mp_tac) >>
         simp[] >> metis_tac[MEM]) >>
     Cases_on `context_read0_opcode i.inst_opcode`
     >- (gvs[context_read0_opcode_def] >>
         `context_read0_opcode i.inst_opcode` by simp[context_read0_opcode_def] >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         drule_all layout_context_reader_trace_step >> metis_tac[]) >>
     Cases_on `MEM i.inst_opcode [SLOAD; TLOAD]`
     >- (gvs[] >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         `?arg. i.inst_operands = [arg]` by
           (qpat_x_assum `inst_wf i` mp_tac >>
            fs[MEM] >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
         drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
           layout_state_read_trace_step >>
         disch_then (drule_at (Pat `g.lop_config = _`)) >>
         disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
         simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
         simp[] >> metis_tac[MEM]) >>
     Cases_on `indexed_context_read_opcode i.inst_opcode`
     >- (gvs[] >>
         `g.lop_cursor < LENGTH (MAP FST path)` by simp[] >>
         `g.lop_anns = (rp,rv)::anns` by metis_tac[] >>
         `?arg. i.inst_operands = [arg]` by
           (qpat_x_assum `inst_wf i` mp_tac >>
            fs[indexed_context_read_opcode_def, MEM] >>
            gvs[inst_wf_def, LENGTH_EQ_NUM_compute]) >>
         drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
           layout_indexed_context_trace_step >>
         disch_then (drule_at (Pat `g.lop_config = _`)) >>
         disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
         simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
         simp[] >> metis_tac[]) >>
     `clean_value_shape i /\ ~MEM i.inst_opcode [ADD; SUB; EQ; LT; GT]` by
       (fs[MEM, indexed_context_read_opcode_def] >> metis_tac[]) >>
     drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
       layout_clean_value_trace_step >>
     disch_then (drule_at (Pat `g.lop_config = _`)) >>
     disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
     simp[] >> disch_then (qspecl_then [`rv`, `rp`, `anns`, `P`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode` by
    (gvs[concretize_inst_with_positions_def, mk_assign_inst_def,
         mk_nop_inst_def, is_terminator_def] >> rpt CASE_TAC >>
     gvs[mk_assign_inst_def, mk_nop_inst_def, is_terminator_def]) >>
  qexists `tpost` >> conj_tac >- metis_tac[] >>
  drule layout_canonical_ordinary_success >>
  disch_then (drule_at (Pat `layout_phase_ok_abort _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  simp[] >> metis_tac[]
QED

val _ = export_theory();
