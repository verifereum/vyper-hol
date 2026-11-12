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
