(* Finite selected-call handoffs at the actual physical control coordinates. *)
Theory functionInlinerLiveSelected
Ancestors
  functionInlinerEntryHandoff functionInlinerLiveInvariant functionInlinerLiveReturn
  functionInlinerSelectedReturn functionInlinerParameterExecution
  functionInlinerEvaluatorResidual functionInlinerFmp
  functionInlinerOperationalCuts functionInlinerParameterSequential
  functionInlinerParameterLocations functionInlinerActivation functionInlinerReachableCuts
  functionInlinerRoutedProvenance functionInlinerOccurrences functionInlinerDefs
  venomExecSemantics venomExecProofs venomState venomInstProps callLayoutDefs
  functionInlinerSimulation functionInlinerFrame venomInstProofs venomInst list pred_set

Theorem inline_parameter_step_effects[local]:
  (is_param_opcode inst.inst_opcode \/ inst.inst_opcode = ASSIGN) /\
  step_inst fuel C inst s = OK t ==>
  inline_shared_frame (t with vs_inst_idx := i) = inline_shared_frame s /\
  inline_caller_residual (t with vs_inst_idx := i) = inline_caller_residual s /\
  (t with vs_inst_idx := i).vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[is_param_opcode_iff] >>
  gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs(),
      update_var_def, inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      inline_caller_residual_def, merge_callee_state_def]
QED

Theorem inline_parameter_sequence_effects:
  !N ts.
    (!k. k < N ==> ?inst t.
      (is_param_opcode inst.inst_opcode \/ inst.inst_opcode = ASSIGN) /\
      step_inst fuel C inst (ts k) = OK t /\
      ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx) ==>
    inline_shared_frame (ts N) = inline_shared_frame (ts 0) /\
    inline_caller_residual (ts N) = inline_caller_residual (ts 0) /\
    (ts N).vs_fmp = (ts 0).vs_fmp
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `inline_shared_frame (ts N) = inline_shared_frame (ts 0) /\
   inline_caller_residual (ts N) = inline_caller_residual (ts 0) /\
   (ts N).vs_fmp = (ts 0).vs_fmp` by
    (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  first_x_assum (qspec_then `N` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[inline_parameter_step_effects]
QED

Theorem inline_parameter_sequence_indices[local]:
  !N ts.
    (!k. k < N ==> ?t.
      ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx) ==>
    !k. k <= N ==> (ts k).vs_inst_idx = (ts 0).vs_inst_idx + k
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[] >> strip_tac >>
  `k < N /\ k <= N` by decide_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >> simp[]
QED

Theorem inline_parameter_interval_effects:
  inline_parameter_interval root ml 0 N /\
  lookup_block ml root.fn_blocks = SOME bb /\ (ts 0).vs_inst_idx = 0 /\
  (!k. k < N ==> ?inst t.
    get_instruction bb (ts k).vs_inst_idx = SOME inst /\
    step_inst fuel C inst (ts k) = OK t /\
    ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx) ==>
  inline_shared_frame (ts N) = inline_shared_frame (ts 0) /\
  inline_caller_residual (ts N) = inline_caller_residual (ts 0) /\
  (ts N).vs_fmp = (ts 0).vs_fmp
Proof
  strip_tac >>
  `!k. k <= N ==> (ts k).vs_inst_idx = k` by
    (mp_tac inline_parameter_sequence_indices >>
     disch_then (qspecl_then [`N`,`ts`] mp_tac) >> simp[] >> metis_tac[]) >>
  irule inline_parameter_sequence_effects >> qexistsl [`C`,`fuel`] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  fs[inline_parameter_interval_def, get_instruction_def, AllCaseEqs()] >>
  metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Theorem inline_parameter_source_prefix_effects:
  param_insts_from 0 params /\
  (!k. k < LENGTH params ==> ?t.
    step_inst fuel C (EL k params) (ss k) = OK t /\
    ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx) ==>
  inline_shared_frame (ss (LENGTH params)) = inline_shared_frame (ss 0) /\
  inline_caller_residual (ss (LENGTH params)) = inline_caller_residual (ss 0) /\
  (ss (LENGTH params)).vs_fmp = (ss 0).vs_fmp
Proof
  strip_tac >> irule inline_parameter_sequence_effects >>
  qexistsl [`C`,`fuel`] >> rpt strip_tac >>
  `param_inst_at k (EL k params)` by metis_tac[param_insts_from_el, arithmeticTheory.ADD]
  >> fs[param_inst_at_def] >> metis_tac[]
QED

Theorem inline_original_child_live_effects[local]:
  inline_original_child C fuel parent occurrence call saved r ca cr /\
  ~saved.vs_halted ==>
  inline_shared_frame ca.ia_entry = inline_shared_frame saved /\
  inline_caller_residual ca.ia_entry = inline_caller_residual saved /\
  ca.ia_entry.vs_fmp = saved.vs_fmp /\ ca.ia_entry.vs_prev_bb = NONE
Proof
  strip_tac >> fs[inline_original_child_def] >>
  drule_all inline_shared_frame_setup >> strip_tac >> simp[] >>
  qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
  simp[setup_callee_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `_ = ca.ia_entry` (fn th => rewrite_tac[GSYM th]) >>
  simp[inline_caller_residual_def, inline_shared_frame_def,
       stateFrameTheory.execution_frame_def, merge_callee_state_def,
       venom_state_component_equality]
QED

Theorem inline_live_selected_entry_trace:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_live_stack C cert root ((p,pa,proute,psnap)::entries) frame /\
  inline_original_child C cfuel pa.ia_id occurrence orig psnap.ils_state r ca cr /\
  inline_call_incidence cert root p pa.ia_function l j orig
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  ca.ia_function.fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  eval_phis ca.ia_entry entry.bb_instructions = OK post /\
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\ d.ic_function = root /\
  MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  frame.ipf_state.vs_current_bb = d.ic_block /\
  frame.ipf_state.vs_inst_idx = d.ic_index /\ ~frame.ipf_state.vs_halted /\
  ss 0 = ca.ia_entry /\
  (!k. k < LENGTH params ==> ?s'.
    step_inst fuel C (EL k params) (ss k) = OK s' /\
    ss (SUC k) = s' with vs_inst_idx := SUC (ss k).vs_inst_idx) ==>
  ?ml bb tb dst v snap ts.
    lookup_block d.ic_block root.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK v /\
    exec_block tfuel Tctx tb frame.ipf_state = OK v /\
    v = jump_to ml frame.ipf_state /\
    v.vs_current_bb = ml /\ v.vs_inst_idx = 0 /\
    lookup_block ml root.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 /\ eval_phis v bb.bb_instructions = OK v /\
    ts 0 = v /\
    (!i. i < LENGTH params ==> ?inst t.
      get_instruction bb (ts i).vs_inst_idx = SOME inst /\
      ~is_terminator inst.inst_opcode /\
      step_inst tfuel Tctx inst (ts i) = OK t /\
      ts (SUC i) = t with vs_inst_idx := SUC (ts i).vs_inst_idx) /\
    exec_block tfuel Tctx bb v = exec_block tfuel Tctx bb (ts (LENGTH params)) /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label (LENGTH params) root ml (LENGTH params) /\
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
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
  `~psnap.ils_state.vs_halted` by
    (drule inline_live_stack_head_shared >>
     simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def,
          venom_state_component_equality]) >>
  drule_all inline_original_child_live_effects >> strip_tac >>
  drule_all inline_selected_entry_handoff >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  drule inline_live_stack_storage >> strip_tac >>
  drule inline_live_stack_lifecycle >> strip_tac >>
  `inline_owner_storage cert ((p,pa,proute,psnap)::entries)
    (frame with ipf_state := v)` by
    (`inline_owner_storage cert
        ((p,pa,proute,psnap with ils_state := psnap.ils_state)::entries)
        (frame with ipf_state := v)` suffices_by simp[] >>
     irule inline_owner_storage_projections >>
     simp[] >> asm_rewrite_tac[jump_to_def] >> simp[]) >>
  drule_at (Pat `inline_call_incidence cert root p fn l j orig outcome`)
    inline_selected_parameters_execute >>
  disch_then (drule_at (Pat `inline_owner_storage cert entries frame`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  drule_all inline_selected_entry_phi_cut >> strip_tac >>
  drule_all inline_parameter_source_prefix_effects >> strip_tac >>
  `ml' = ml /\ mj = 0` by
    metis_tac[inline_parameter_boundary_path_functional] >>
  `bb' = bb` by metis_tac[optionTheory.SOME_11] >>
  `ts 0 = v` by fs[] >>
  `inline_shared_frame (ts (LENGTH params)) = inline_shared_frame (ts 0) /\
   inline_caller_residual (ts (LENGTH params)) = inline_caller_residual (ts 0) /\
   (ts (LENGTH params)).vs_fmp = (ts 0).vs_fmp` by
    (irule inline_parameter_interval_effects >>
     metis_tac[]) >>
  qexistsl [`ml`,`bb`,`tb`,`dst`,`v`,`snap`,`ts`] >>
  simp[] >>
  reverse (rpt conj_tac)
  >- (fs[inline_live_stack_def] >>
      simp[inline_live_stack_def] >>
      `v.vs_fmp = frame.ipf_state.vs_fmp` by
        simp[jump_to_def] >>
      metis_tac[]) >>
  metis_tac[optionTheory.SOME_11]
QED

(* Compatibility projection; the execution proof lives in the trace export. *)
Theorem inline_live_selected_entry:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_live_stack C cert root ((p,pa,proute,psnap)::entries) frame /\
  inline_original_child C cfuel pa.ia_id occurrence orig psnap.ils_state r ca cr /\
  inline_call_incidence cert root p pa.ia_function l j orig
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  ca.ia_function.fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  eval_phis ca.ia_entry entry.bb_instructions = OK post /\
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\ d.ic_function = root /\
  MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  frame.ipf_state.vs_current_bb = d.ic_block /\
  frame.ipf_state.vs_inst_idx = d.ic_index /\ ~frame.ipf_state.vs_halted /\
  ss 0 = ca.ia_entry /\
  (!k. k < LENGTH params ==> ?s'.
    step_inst fuel C (EL k params) (ss k) = OK s' /\
    ss (SUC k) = s' with vs_inst_idx := SUC (ss k).vs_inst_idx) ==>
  ?ml bb tb dst v snap ts.
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
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
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
  strip_tac >> drule_all inline_live_selected_entry_trace >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  qexistsl [`ml`,`bb`,`tb`,`dst`,`v`,`snap`,`ts`] >> asm_rewrite_tac[]
QED

(* The adapter coordinates remain explicit: the evaluator join must supply
   these actual coordinates before using the execution equation. *)
Theorem inline_live_selected_return:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_live_stack C cert root
    ((q,ca,route,snap)::(p,pa,proute,psnap)::rest) frame /\
  inline_call_incidence cert root p pa.ia_function l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert p proute.ir_rename pa.ia_function /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  lookup_block rl ca.ia_function.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] /\ ret.inst_operands = ops ++ [pc] /\
  step_inst fuel C ret snap.ils_state = IntRet ir s' /\ ~frame.ipf_state.vs_halted /\
  lookup_function nm C.ctx_functions = SOME ca.ia_function /\
  setup_callee ca.ia_function args psnap.ils_state = SOME ca.ia_entry /\
  run_blocks cfuel C ca.ia_function ca.ia_entry = IntRet ir s' /\
  ~ca.ia_entry.vs_halted ==>
  ?ml mj bb caller'.
    let writes = FOLDL (\s (x,w). update_var x w s) frame.ipf_state
          (ZIP (MAP proute.ir_rename call.inst_outputs,ir.iret_values));
        target = jump_to (inline_path_rename zipper e.ise_return) writes;
        resumed = adopt_return_fmp ir (merge_callee_state caller' s');
        psnap' = psnap with <|ils_state := resumed;
          ils_defined := set call.inst_outputs UNION psnap.ils_defined|> in
    lookup_block ml root.fn_blocks = SOME bb /\
    (frame.ipf_state.vs_current_bb = ml /\ frame.ipf_state.vs_inst_idx = mj ==>
      exec_block tfuel Tctx bb frame.ipf_state = OK target) /\
    bind_outputs call.inst_outputs ir.iret_values psnap.ils_state = SOME caller' /\
    inline_live_stack C cert root ((p,pa,proute,psnap')::rest)
      (frame with ipf_state := target) /\
    target.vs_current_bb = inline_path_rename zipper e.ise_return /\
    target.vs_prev_bb = SOME frame.ipf_state.vs_current_bb /\ target.vs_inst_idx = 0 /\
    inline_parameter_boundary_path zipper e.ise_final e.ise_return 0 root
      (inline_path_rename zipper e.ise_return) 0 /\
    (?continuation. lookup_block (inline_path_rename zipper e.ise_return)
      root.fn_blocks = SOME continuation) /\
    (!path. inline_routed_leaf cert root q ca.ia_function path ==> ?counter.
      inline_path_location path
        (SOME <|il_block := rl; il_phase := InlineAtInstruction ri; il_counter := 0|>) =
      SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := counter|>)
Proof
  strip_tac >>
  drule inline_live_stack_storage >> strip_tac >>
  drule inline_live_stack_lifecycle >> strip_tac >>
  drule inline_owner_storage_head >> strip_tac >>
  drule inline_selected_return_execute >>
  disch_then (drule_at (Pat `inline_call_incidence cert root p fn l j call outcome`)) >>
  disch_then (drule_at (Pat `inline_owner_storage cert entries frame`)) >>
  disch_then (drule_at (Pat `inline_tracked_snapshot child ca route snap frame`)) >>
  pure_rewrite_tac[REFL_CLAUSE, AND_CLAUSES] >> disch_then drule_all >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  pop_assum mp_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `raw_return_user_arity ret = SOME (LENGTH call.inst_outputs)` by
    metis_tac[functionInlinerReturnRoutingTheory.inline_selected_return_arity, MEM] >>
  `inline_shared_frame s' = inline_shared_frame frame.ipf_state` by
    (drule_all functionInlinerReturnTransportTheory.inline_return_source >>
     strip_tac >> gvs[] >> metis_tac[inline_live_stack_head_shared]) >>
  `inline_caller_residual frame.ipf_state = inline_caller_residual psnap.ils_state` by
    metis_tac[inline_live_stack_member_residual, MEM] >>
  qexistsl [`ml`,`mj`,`bb`,`caller'`] >> simp[LET_THM] >>
  qmatch_goalsub_abbrev_tac `jump_to dest writes` >>
  `bind_outputs (MAP proute.ir_rename call.inst_outputs) ir.iret_values
      frame.ipf_state = SOME writes` by
    (qpat_x_assum `bind_outputs call.inst_outputs _ _ = _` mp_tac >>
     simp[bind_outputs_def, Abbr `writes`] >> metis_tac[]) >>
  `inline_shared_frame (adopt_return_fmp ir (merge_callee_state caller' s')) =
      inline_shared_frame (jump_to dest writes)` by
    (irule inline_source_return_shared_bind_jump >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  `inline_shared_frame writes = inline_shared_frame frame.ipf_state` by
    (irule venomInstProofs1Theory.bind_outputs_preserves >> simp[] >> goal_assum (drule_at Any)) >>
  `writes.vs_fmp = frame.ipf_state.vs_fmp` by
    (irule venomInstProofs1Theory.bind_outputs_preserves >> simp[update_var_def] >>
     goal_assum (drule_at Any)) >>
  `inline_caller_residual (jump_to dest writes) =
      inline_caller_residual frame.ipf_state` by
    (`inline_shared_frame (jump_to dest writes) =
        inline_shared_frame frame.ipf_state` by
       (qpat_x_assum `inline_shared_frame writes = _` (fn th =>
          rewrite_tac[GSYM th]) >>
        simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def, jump_to_def]) >>
     irule inline_caller_residual_shared >> goal_assum (drule_at Any)) >>
  simp[inline_live_stack_def] >>
  qpat_x_assum `inline_live_stack _ _ _ _ _` mp_tac >>
  simp[inline_live_stack_def] >> strip_tac >>
  `s'.vs_fmp = frame.ipf_state.vs_fmp` by
    (qpat_x_assum `inline_shared_frame s' = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_fmp``) >>
     simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def]) >>
  `inline_caller_residual caller' = inline_caller_residual psnap.ils_state` by
    (irule venomInstProofs1Theory.bind_outputs_preserves >>
     simp[inline_caller_residual_def, update_var_def, merge_callee_state_def,
          inline_shared_frame_def, stateFrameTheory.execution_frame_def] >>
     metis_tac[]) >>
  simp[jump_to_def]
QED

(* At a recursively established mapped cut the retained layout witness fixes
   the adapter coordinates, so execution starts from the actual frame. *)
Theorem inline_live_selected_return_at_cut:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_live_stack C cert root
    ((q,ca,route,snap)::(p,pa,proute,psnap)::rest) frame /\
  inline_call_incidence cert root p pa.ia_function l j call (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert p proute.ir_rename pa.ia_function /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  lookup_block rl ca.ia_function.fn_blocks = SOME rb /\ get_instruction rb ri = SOME ret /\
  MEM ret.inst_opcode [RET; RETFMP] /\ ret.inst_operands = ops ++ [pc] /\
  step_inst fuel C ret snap.ils_state = IntRet ir s' /\ ~frame.ipf_state.vs_halted /\
  lookup_function nm C.ctx_functions = SOME ca.ia_function /\
  setup_callee ca.ia_function args psnap.ils_state = SOME ca.ia_entry /\
  run_blocks cfuel C ca.ia_function ca.ia_entry = IntRet ir s' /\
  ~ca.ia_entry.vs_halted /\
  inline_live_location cert root q ca path
    (InlineAtInstruction snap.ils_state.vs_inst_idx)
    (InlineAtInstruction frame.ipf_state.vs_inst_idx) counter snap.ils_state frame.ipf_state /\
  snap.ils_state.vs_current_bb = rl /\ snap.ils_state.vs_inst_idx = ri ==>
  ?bb caller'.
    let writes = FOLDL (\s (x,w). update_var x w s) frame.ipf_state
          (ZIP (MAP proute.ir_rename call.inst_outputs,ir.iret_values));
        target = jump_to (inline_path_rename zipper e.ise_return) writes;
        resumed = adopt_return_fmp ir (merge_callee_state caller' s');
        psnap' = psnap with <|ils_state := resumed;
          ils_defined := set call.inst_outputs UNION psnap.ils_defined|> in
    lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME bb /\
    exec_block tfuel Tctx bb frame.ipf_state = OK target /\
    bind_outputs call.inst_outputs ir.iret_values psnap.ils_state = SOME caller' /\
    inline_live_stack C cert root ((p,pa,proute,psnap')::rest)
      (frame with ipf_state := target) /\
    target.vs_current_bb = inline_path_rename zipper e.ise_return /\
    target.vs_prev_bb = SOME frame.ipf_state.vs_current_bb /\ target.vs_inst_idx = 0 /\
    inline_parameter_boundary_path zipper e.ise_final e.ise_return 0 root
      (inline_path_rename zipper e.ise_return) 0 /\
    (?continuation. lookup_block (inline_path_rename zipper e.ise_return)
      root.fn_blocks = SOME continuation)
Proof
  strip_tac >> drule_all inline_live_selected_return >>
  disch_then (qspecl_then [`tfuel`,`Tctx`] strip_assume_tac) >>
  fs[inline_live_location_def] >>
  `?next. inline_path_location path
      (SOME <|il_block := rl; il_phase := InlineAtInstruction ri; il_counter := 0|>) =
    SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := next|>` by
    metis_tac[] >>
  `frame.ipf_state.vs_current_bb = ml /\ frame.ipf_state.vs_inst_idx = mj` by
    gvs[] >>
  simp[]
QED
