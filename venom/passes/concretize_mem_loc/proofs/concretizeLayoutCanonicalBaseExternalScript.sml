Theory concretizeLayoutCanonicalBaseExternal
Ancestors concretizeLayoutCanonicalBase concretizeLayoutCanonicalDriver
  concretizeLayoutSelectedBaseInterface concretizeLayoutCompletedJump
  ptrDiscipline venomExecSemantics venomInst list
  concretizeLayoutPhaseExternal concretizeStepStructure concretizeLayoutLocalReturn
  frameRelocationBinding venomWf o1PassContract frameFiniteJointDecoration
  concretizeLayoutPhaseOrigin

(* Leaf of the exhaustive base certificate: successful external calls and
   creates, in the shape of layout_canonical_ordinary_nonterm_success. *)

Theorem layout_canonical_external_success:
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
  MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
  step_inst_base i s = OK post ==>
  ?tpost. step_inst_base j t = OK tpost /\
    layout_canonical_success D lo vs0 C C' q0 es qs ass qend n F (INL g) post tpost
Proof
  strip_tac >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> ALLOCA /\
   i.inst_opcode <> NOP` by
    (fs[MEM] >> simp[is_terminator_def]) >>
  drule_all layout_canonical_ordinary_environment >> strip_tac >>
  `j = i` by (gvs[concretize_positions_unchanged] >> fs[MEM]) >>
  qpat_x_assum `j = i` SUBST_ALL_TAC >>
  qpat_x_assum `es = _` SUBST_ALL_TAC >>
  qpat_x_assum `qs = _` SUBST_ALL_TAC >>
  qpat_x_assum `q = JointConfig _ _ _ _ _ _ _ _ _ _ _` SUBST_ALL_TAC >>
  qpat_x_assum `g.lop_cursor = n` (SUBST_ALL_TAC o SYM) >>
  drule layout_canonical_ordinary_edge >>
  disch_then (drule_at (Pat `layout_ordinary_trace _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`post`, `i`] mp_tac) >> simp[] >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[o1_fn_shape_def, wf_function_def] >>
  `active_inst fn i s` by fs[decoration_at_def] >>
  `~in_revert_forward fn s` by
    (irule active_inst_not_revert_forward >> simp[] >> qexists `i` >> fs[MEM]) >>
  `~joint_read_exempt (EL g.lop_cursor (q0::MAP SND path))` by
    fs[layout_ordinary_trace_def, joint_read_exempt_def] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_external_trace_step >>
  disch_then (drule_at (Pat `_ .lop_config = JointConfig _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_pass_stage _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `callee_first _ _`)) >>
  disch_then (drule_at (Pat `EVERY (fn_ptr_ok _) _`)) >>
  disch_then (drule_at (Pat `_ .lop_ids = _ :: _`)) >>
  disch_then (drule_at (Pat `_ .lop_anns = _ :: _`)) >>
  disch_then (drule_at (Pat `EL _ _ = SOME (OriginOrdinary _ _)`)) >>
  simp[] >> (impl_tac >- fs[MEM]) >> strip_tac >>
  qexists `tpost` >> simp[] >>
  irule layout_canonical_ordinary_success >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
