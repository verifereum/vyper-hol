(* Selected jumps land at the total parameter boundary, without resetting
   physical control.  Block-entry PHIs are checked separately below. *)
Theory functionInlinerEntryHandoff
Ancestors
  functionInlinerEntryExecution functionInlinerParameterExecution
  functionInlinerParameterLocations functionInlinerReachableCuts
  functionInlinerDefs functionInlinerActivation functionInlinerLocation
  functionInlinerRoutedProvenance functionInlinerPairedSelection
  functionInlinerSelectedParameterDescriptors functionInlinerOccurrences
  functionInlinerFrame callLayoutDefs functionInlinerParameterNesting
  functionInlinerEnvelopes algebraicOptMainEntryProofs
  venomExecSemantics venomExecProofs venomInst venomState list

Theorem inline_parameter_boundary_zero:
  inline_parameter_boundary choice fn l 0 root ml mj ==>
  ml = inline_choice_rename choice l /\ mj = 0
Proof
  Cases_on `choice` >>
  simp[inline_parameter_boundary_def, inline_keep_boundary_def,
    inline_choice_rename_def, inline_cell_prefix_def,
    rewrite_inline_insts_def] >> rpt strip_tac >> gvs[]
QED

Theorem inline_parameter_boundary_path_zero:
  !path fn l root ml mj.
    inline_parameter_boundary_path path fn l 0 root ml mj ==>
    ml = inline_path_rename path l /\ mj = 0
Proof
  Induct >> simp[inline_parameter_boundary_path_def, inline_path_rename_def] >>
  rpt strip_tac >> drule inline_parameter_boundary_zero >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[combinTheory.o_DEF]
QED

Theorem inline_parameter_boundary_cell_action:
  !frames fn l root ml mj.
    inline_parameter_boundary_path
      (MAP (\(tag,next). inline_cell_choice tag) frames) fn l 0 root ml mj ==>
    ml = inline_cell_label_action frames l /\ mj = 0
Proof
  Induct >> simp[inline_parameter_boundary_path_def, inline_cell_label_action_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> Cases_on `h0` >>
  simp[inline_cell_choice_def, inline_parameter_boundary_path_def,
    inline_cell_label_action_def, inline_parameter_boundary_def,
    inline_keep_boundary_def, inline_cell_prefix_def, rewrite_inline_insts_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[] >>
  `MEM l (fn_labels i.ise_callee)` by
    (qpat_x_assum `lookup_block l i.ise_callee.fn_blocks = SOME cb` mp_tac >>
     simp[lookup_block_def] >> strip_tac >>
     drule FIND_MEM >> drule FIND_P >> simp[fn_labels_def, MEM_MAP] >>
     rpt strip_tac >> qexists `cb` >> simp[]) >> simp[]
QED

Theorem inline_selected_parameter_entry_label:
  inline_annotated_origin ctx n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks ==>
  eb.bb_label = STRCAT e.ise_prefix entry.bb_label
Proof
  strip_tac >>
  drule inline_selected_paired_separation >> simp[] >> disch_then drule >>
  simp[] >> strip_tac >>
  `child = inline_entry_function b` by metis_tac[inline_selected_child_identity] >>
  fs[] >>
  drule_all functionInlinerEntryParametersTheory.inline_annotated_entry_parameter_address >>
  strip_tac >>
  qpat_x_assum `(clone_function _ _).fn_blocks = _` mp_tac >>
  simp[clone_function_def] >>
  Cases_on `e.ise_callee.fn_blocks` >> simp[clone_basic_block_def] >>
  strip_tac >> gvs[]
QED

Theorem inline_selected_entry_handoff:
  inline_annotated_origin ctx n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\ d.ic_function = root /\
  MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  t.vs_current_bb = d.ic_block /\ t.vs_inst_idx = d.ic_index /\ ~t.vs_halted ==>
  ?ml bb tb dst v.
    inline_parameter_interval root ml 0 (LENGTH params) /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label 0 root ml 0 /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label (LENGTH params) root ml (LENGTH params) /\
    lookup_block ml root.fn_blocks = SOME bb /\
    lookup_block d.ic_block root.fn_blocks = SOME tb /\
    get_instruction tb d.ic_index = SOME dst /\
    step_inst fuel Tctx dst t = OK v /\ exec_block fuel Tctx tb t = OK v /\
    v = jump_to ml t /\ v.vs_current_bb = ml /\ v.vs_inst_idx = 0 /\
    v.vs_prev_bb = SOME t.vs_current_bb /\ ~v.vs_halted /\
    v = v with <|vs_current_bb := ml; vs_inst_idx := 0|> /\
    inline_shared_frame v = inline_shared_frame t /\
    inline_caller_residual v = inline_caller_residual t
Proof
  strip_tac >>
  drule_all inline_selected_parameter_interval >> strip_tac >>
  `eb.bb_label = STRCAT e.ise_prefix entry.bb_label` by
    (irule inline_selected_parameter_entry_label >> metis_tac[]) >>
  `ml = inline_cell_label_action frames eb.bb_label /\ mj = 0` by
    (qpat_x_assum `inline_parameter_boundary_path _ _ _ 0 _ _ _` mp_tac >>
     simp[inline_parameter_boundary_path_def, inline_parameter_boundary_def,
       inline_cell_prefix_def, rewrite_inline_insts_def] >> strip_tac >>
     metis_tac[inline_parameter_boundary_cell_action]) >>
  drule_all inline_selected_entry_exec_block >>
  disch_then (qspecl_then [`fuel`,`Tctx`] strip_assume_tac) >>
  gvs[] >> simp[jump_to_def, venom_state_component_equality]
QED

Theorem inline_entry_keep_prefix_rename[local]:
  !prefix. EVERY (\c. ?e. c = InlineKeep e) prefix ==>
    inline_path_rename prefix = I
Proof
  Induct >> simp[inline_path_rename_def] >> rpt strip_tac >>
  gvs[inline_path_rename_def, inline_choice_rename_def, combinTheory.o_DEF,
    FUN_EQ_THM]
QED

(* Successful initial source PHIs have an empty prefix: setup_callee has
   no predecessor.  This also covers an empty parameter prefix.  Transport
   that length on the genuine child route; no predecessor equation is
   needed for this empty batch. *)
Theorem inline_selected_entry_phi_cut:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\
  inline_parameter_boundary_path (InlineEnter e::zipper)
    e.ise_callee entry.bb_label 0 root ml mj /\
  source.vs_prev_bb = NONE /\ eval_phis source entry.bb_instructions = OK post ==>
  ?bb. lookup_block ml root.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 /\ mj = 0 /\
    (!v. eval_phis v bb.bb_instructions = OK v /\
      (v with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      (v with vs_inst_idx := mj))
Proof
  strip_tac >>
  `phi_prefix_length entry.bb_instructions = 0` by
    metis_tac[algebraicOptMainEntryProofsTheory.ao_eval_phis_initial_prefix] >>
  drule inline_selected_entry_route_pair >> simp[] >> disch_then drule >>
  simp[] >> strip_tac >>
  `child' = child` by (fs[inline_namespace_leaf_at_def] >>
     imp_res_tac inline_namespace_node_same_address >>
     qpat_x_assum `InlineNamespaceLeaf child' = InlineNamespaceLeaf child` mp_tac >>
     simp[NoAsms]) >>
  gvs[] >>
  `lookup_block entry.bb_label child.fn_blocks = SOME entry` by
    simp[lookup_block_def, FIND_thm] >>
  `inline_path_rename prefix = I` by metis_tac[inline_entry_keep_prefix_rename] >>
  drule_all inline_routed_phi_prefix_length >>
  disch_then (qspec_then `NONE` mp_tac) >>
  simp[inline_phi_entry_path_label, inline_path_rename_append,
    inline_path_rename_def, inline_choice_rename_def, combinTheory.o_DEF] >>
  strip_tac >>
  drule inline_parameter_boundary_path_zero >>
  simp[inline_path_rename_def, inline_choice_rename_def, combinTheory.o_DEF] >>
  strip_tac >> gvs[] >> gen_tac >>
  irule analysisSimProofsBaseTheory.phi_prefix_length_zero_eval_phis_ok >>
  simp[]
QED
