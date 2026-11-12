Theory concretizeLayoutSelectedPairedResume
Ancestors concretizeLayoutSelectedResume concretizeLayoutPairedEntry
  concretizeLayoutAlignedControl concretizeLayoutBlockPairing
  concretizeLayoutPhaseOrigin concretizeStepStructure frameControlAgreement
  venomState venomInst arithmetic list

Theorem layout_selected_resume_paired_entry:
  layout_paired_ordinary D lo vs0 C C' q0 es qs q positions
    a.lop_config a.lop_cursor bb caller bb' caller' a /\
  a.lop_config = JointConfig stk PG G caller_tn fn call caller oms om hs h /\
  a.lop_ids = birth::ids /\ a.lop_anns = (rp,rv)::anns /\
  a.lop_ids = EL a.lop_cursor iss /\ a.lop_anns = EL a.lop_cursor ass /\
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
  b.lop_ids = EL b.lop_cursor iss /\ b.lop_anns = EL b.lop_cursor ass /\
  es = MAP FST path /\ qs = MAP SND path /\ vs0.vs_allocas = FEMPTY /\
  b.lop_cursor < LENGTH es /\
  EL b.lop_cursor es = SOME (OriginResume fuel callee inst sc ret sc post) /\
  (!k. k < LENGTH path ==>
    resolved_annotation_edge C k (EL k (q0::MAP SND path)) (FST (EL k path))
      (EL (SUC k) (q0::MAP SND path)) (EL k iss) (EL k ass)
      (EL (SUC k) iss) (EL (SUC k) ass)) /\
  bind_outputs call.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller sc)) = SOME post /\
  bind_outputs call.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state caller' tc)) = SOME post' ==>
  layout_paired_ordinary D lo vs0 C C' q0 es qs q positions
    (EL (SUC b.lop_cursor) (q0::qs)) (SUC b.lop_cursor)
    bb (post with vs_inst_idx := SUC caller.vs_inst_idx)
    bb' (post' with vs_inst_idx := SUC caller'.vs_inst_idx)
    (a with <| lop_pending := F; lop_cursor := SUC b.lop_cursor;
      lop_bound := SUC b.lop_bound;
      lop_config := EL (SUC b.lop_cursor) (q0::qs);
      lop_ids := EL (SUC b.lop_cursor) iss;
      lop_anns := EL (SUC b.lop_cursor) ass;
      lop_target_taint := b.lop_target_taint with
        t_var := DRESTRICT a.lop_target_taint.t_var (COMPL (set call.inst_outputs)) |>)
Proof
  strip_tac >>
  `~a.lop_pending /\
   a.lop_origin.lbo_source = bb /\ a.lop_origin.lbo_target = bb' /\
   layout_ordinary_entry D lo vs0 C C' q0 es qs q a caller caller' /\
   control_agree caller caller' /\
   layout_block_pair positions bb bb' caller.vs_inst_idx caller'.vs_inst_idx` by
    fs[layout_paired_ordinary_def, layout_aligned_entry_def] >>
  `control_agree (post with vs_inst_idx := SUC caller.vs_inst_idx)
     (post' with vs_inst_idx := SUC caller'.vs_inst_idx)` by
    (irule layout_aligned_caller_restore >> metis_tac[]) >>
  `layout_block_pair positions bb bb' (SUC caller.vs_inst_idx)
     (SUC caller'.vs_inst_idx)` by
    (drule_all layout_block_pair_advance >>
     simp[concretize_positions_unchanged, ADD1]) >>
  `get_instruction a.lop_origin.lbo_source caller.vs_inst_idx = SOME call` by
    metis_tac[] >>
  drule_all layout_selected_resume_entry >> strip_tac >>
  simp[layout_paired_ordinary_def, layout_aligned_entry_def]
QED
