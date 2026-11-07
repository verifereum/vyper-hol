Theory concretizeLayoutCanonicalResume
Ancestors concretizeLayoutCanonicalDriver concretizeLayoutSelectedPairedResume
  concretizeLayoutCanonicalIndex concretizeLayoutPairedEntry
  concretizeLayoutAlignedControl concretizeLayoutPhaseOrigin
  concretizeLayoutEntryFlags frameControlAgreement arithmetic list

(* The caller and RET endpoint share the same ambient annotation sequence.
   This consumer also preserves the independent structural instruction ranks. *)
Theorem layout_canonical_resume_paired:
  layout_paired_ordinary D lo vs0 C C' q0 es qs q positions
    a.lop_config a.lop_cursor bb caller bb' caller' a /\
  layout_driver_indexed es ass a /\ layout_driver_indexed es ass b /\
  a.lop_config = JointConfig stk PG G caller_tn fn call caller oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\ setup_callee callee args caller = SOME cs /\
  get_instruction bb caller.vs_inst_idx = SOME call /\
  joint_transition C a.lop_config NONE qc /\
  selected_segment C q0 path a.lop_cursor a.lop_config ((NONE,qc)::w) b.lop_config /\
  decorated_run C callee cs (IntRet ret sc) qc (SUC a.lop_cursor) w b.lop_config dc /\
  b.lop_cursor = SUC a.lop_cursor + LENGTH w /\
  layout_ret_endpoint D lo vs0 C C' q0 es qs q b sc tc ret ret' /\
  b.lop_config = JointConfig cstk cPG cG tn callee inst sc coms com chs ch /\
  inst.inst_opcode = RET /\
  es = MAP FST path /\ qs = MAP SND path /\ vs0.vs_allocas = FEMPTY /\
  b.lop_cursor < LENGTH es /\
  EL b.lop_cursor es = SOME (OriginResume fuel callee inst sc ret sc post) /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path))
      (EL k (lifetime_annotations 0 [0] es)) (EL k ass)
      (EL (SUC k) (lifetime_annotations 0 [0] es)) (EL (SUC k) ass)) /\
  bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post /\
  bind_outputs call.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' ==>
  ?c. c.lop_origin = a.lop_origin /\
    layout_canonical_entry D lo vs0 C C' q0 es qs ass q
      (EL (SUC b.lop_cursor) (q0::qs)) (SUC b.lop_cursor) (INL c)
      (post with vs_inst_idx := SUC post.vs_inst_idx)
      (post' with vs_inst_idx := SUC post'.vs_inst_idx) /\
    layout_paired_ordinary D lo vs0 C C' q0 es qs q positions
      (EL (SUC b.lop_cursor) (q0::qs)) (SUC b.lop_cursor)
      bb (post with vs_inst_idx := SUC post.vs_inst_idx)
      bb' (post' with vs_inst_idx := SUC post'.vs_inst_idx) c
Proof
  strip_tac >>
  `a.lop_ids = EL a.lop_cursor (lifetime_annotations 0 [0] es) /\
   a.lop_anns = EL a.lop_cursor ass /\
   b.lop_ids = EL b.lop_cursor (lifetime_annotations 0 [0] es) /\
   b.lop_anns = EL b.lop_cursor ass` by
    fs[layout_driver_indexed_def, layout_phase_canonical_def] >>
  drule_all layout_selected_resume_paired_entry >> strip_tac >>
  `post.vs_inst_idx = caller.vs_inst_idx /\
   post'.vs_inst_idx = caller'.vs_inst_idx` by
    (imp_res_tac venomExecSemanticsTheory.bind_outputs_inst_idx >>
     gvs[venomExecSemanticsTheory.adopt_return_fmp_def,
         venomExecSemanticsTheory.merge_callee_state_def] >>
     rpt CASE_TAC >> gvs[]) >>
  qpat_assum `post.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
  qpat_assum `post'.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
  goal_assum (drule_at Any) >>
  gvs[layout_canonical_entry_def, layout_canonical_ready_def,
      layout_driver_indexed_def, layout_phase_canonical_def,
      layout_paired_ordinary_def, layout_aligned_entry_def,
      layout_ordinary_entry_def]
QED

(* At INVOKE the resume edge has already been consumed: the output witness
   is ready, and the operational instruction increment is part of the entry. *)
Theorem layout_canonical_resume_success:
  c.lop_origin = a.lop_origin /\
  layout_canonical_entry D lo vs0 C C' q0 es qs ass q qe (SUC m) (INL c)
    (post with vs_inst_idx := SUC post.vs_inst_idx)
    (post' with vs_inst_idx := SUC post'.vs_inst_idx) ==>
  layout_canonical_success D lo vs0 C C' q0 es qs ass q m T (INL a) post post'
Proof
  strip_tac >>
  `post.vs_halted = post'.vs_halted` by
    (drule layout_canonical_entry_forget >>
     simp[concretizeLayoutScopedPhaseTheory.layout_scoped_entry_def] >>
     strip_tac >> drule layout_ordinary_entry_halted_agree >> simp[]) >>
  simp[layout_canonical_success_def] >> qexists `INL c` >>
  gvs[layout_canonical_entry_def, layout_canonical_ready_def,
      layout_phase_origin_def]
QED

val _ = export_theory();
