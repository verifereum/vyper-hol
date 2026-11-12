(* Completed original child evaluations supply the finite selected entry cut. *)
Theory functionInlinerSelectedSource
Ancestors
  functionInlinerSourcePrefix functionInlinerLiveSelected
  functionInlinerActivation venomExecSemantics venomExecProofs
  venomInst list passSimulationDefs

Theorem inline_original_child_entry_result[local]:
  inline_original_child C cfuel pa occurrence orig saved r ca res /\
  ca.ia_function.fn_blocks = entry::rest ==>
  ?k post bres.
    cfuel = SUC k /\
    lookup_block ca.ia_entry.vs_current_bb ca.ia_function.fn_blocks = SOME entry /\
    ca.ia_entry.vs_prev_bb = NONE /\ ca.ia_entry.vs_inst_idx = 0 /\
    eval_phis ca.ia_entry entry.bb_instructions = OK post /\
    exec_block k C entry
      (post with vs_inst_idx := phi_prefix_length entry.bb_instructions) = bres /\
    (!err. bres <> Error err) /\
    res = (case bres of
      OK z => if z.vs_halted then Halt z else run_blocks k C ca.ia_function z
    | IntRet ir z => IntRet ir z | other => other)
Proof
  strip_tac >>
  qpat_x_assum `inline_original_child _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[inline_original_child_def] >> strip_tac >>
  `ca.ia_entry.vs_current_bb = entry.bb_label /\
   ca.ia_entry.vs_prev_bb = NONE /\ ca.ia_entry.vs_inst_idx = 0` by
    (qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
     simp[setup_callee_def] >> strip_tac >>
     qpat_x_assum `_ = ca.ia_entry` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `lookup_block ca.ia_entry.vs_current_bb ca.ia_function.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  Cases_on `cfuel` >- gvs[Once run_blocks_def, terminates_def] >>
  mp_tac (Q.SPECL [`ca.ia_entry`,`entry.bb_instructions`]
    eval_phis_ok_or_error_defs) >> strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = res` mp_tac >>
  asm_rewrite_tac[Once run_blocks_def] >> strip_tac >>
  gvs[terminates_def] >>
  rename1 `eval_phis ca.ia_entry entry.bb_instructions = OK post` >>
  Cases_on `exec_block n C entry
    (post with vs_inst_idx := phi_prefix_length entry.bb_instructions)` >>
  gvs[terminates_def]
QED

Theorem inline_live_selected_source_entry:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_live_stack C cert root ((p,pa,proute,psnap)::entries) frame /\
  inline_original_child C cfuel pa.ia_id occurrence orig psnap.ils_state r ca res /\
  inline_call_incidence cert root p pa.ia_function l j orig
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  ca.ia_function.fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\ d.ic_function = root /\
  MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  frame.ipf_state.vs_current_bb = d.ic_block /\
  frame.ipf_state.vs_inst_idx = d.ic_index /\ ~frame.ipf_state.vs_halted ==>
  ?k post bres ss ml bb tb dst v snap ts.
    cfuel = SUC k /\
    run_blocks cfuel C ca.ia_function ca.ia_entry = res /\
    lookup_block ca.ia_entry.vs_current_bb ca.ia_function.fn_blocks = SOME entry /\
    eval_phis ca.ia_entry entry.bb_instructions = OK post /\
    phi_prefix_length entry.bb_instructions = 0 /\ post = ca.ia_entry /\
    exec_block k C entry
      (post with vs_inst_idx := phi_prefix_length entry.bb_instructions) = bres /\
    (!err. bres <> Error err) /\
    res = (case bres of
      OK z => if z.vs_halted then Halt z else run_blocks k C ca.ia_function z
    | IntRet ir z => IntRet ir z | other => other) /\
    ss 0 = ca.ia_entry /\
    (!i. i < LENGTH params ==> ?s'.
      step_inst k C (EL i params) (ss i) = OK s' /\
      ss (SUC i) = s' with vs_inst_idx := SUC (ss i).vs_inst_idx) /\
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
    exec_block k C entry (ss (LENGTH params)) = bres /\
    lookup_block d.ic_block root.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK v /\
    exec_block tfuel Tctx tb frame.ipf_state = OK v /\
    v = jump_to ml frame.ipf_state /\
    v.vs_current_bb = ml /\ v.vs_inst_idx = 0 /\
    lookup_block ml root.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 /\ eval_phis v bb.bb_instructions = OK v /\
    ts 0 = v /\
    exec_block tfuel Tctx bb v = exec_block tfuel Tctx bb (ts (LENGTH params)) /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label (LENGTH params) root ml (LENGTH params) /\
    (ts (LENGTH params)).vs_current_bb = ml /\
    (ts (LENGTH params)).vs_inst_idx = LENGTH params /\
    snap.ils_saved = psnap.ils_state /\
    snap.ils_protected = (psnap.ils_defined DIFF psnap.ils_opaque) DIFF set orig.inst_outputs /\
    snap.ils_parent_rename = proute.ir_rename /\
    inline_live_stack C cert root
      ((q,ca,route,snap with <|ils_state := ss (LENGTH params);
        ils_defined := set (FLAT (MAP (\i. i.inst_outputs) params))|>)::
       (p,pa,proute,psnap)::entries)
      (frame with ipf_state := ts (LENGTH params))
Proof
  strip_tac >>
  drule_all inline_original_child_entry_result >> strip_tac >>
  drule_all inline_source_entry_parameter_prefix >> strip_tac >>
  drule_all inline_live_selected_entry >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  qexistsl [`k`,`post`,`bres`,`ss`,`ml`,`bb`,`tb`,`dst`,`v`,`snap`,`ts`] >>
  asm_rewrite_tac[] >>
  fs[inline_original_child_def]
QED
