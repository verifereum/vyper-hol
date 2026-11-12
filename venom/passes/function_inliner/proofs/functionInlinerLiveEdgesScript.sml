(* Actual branch predecessors, distinct from the storage renaming action. *)
Theory functionInlinerLiveEdges
Ancestors
  functionInlinerOperationalCuts functionInlinerLiveInvariant
  functionInlinerPhiTransport functionInlinerWf venomExecProps
  passSimulationProps functionInlinerActivation functionInlinerReachableCuts
  functionInlinerLocation functionInlinerSiteLayout functionInlinerRoutedProvenance
  functionInlinerDefs venomWf venomInst venomState venomExecSemantics list rich_list

Theorem inline_edge_site_shape:
  inline_site_edit_valid e /\ wf_function e.ise_caller /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb ==>
  bb_well_formed bb /\ e.ise_index + 1 < LENGTH bb.bb_instructions /\
  (EL e.ise_index bb.bb_instructions).inst_opcode = INVOKE
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels e.ise_caller)` by gvs[wf_function_def] >>
  `find_invoke_site e.ise_callee.fn_name e.ise_caller.fn_blocks =
    SOME (e.ise_block,e.ise_index)` by gvs[inline_site_edit_valid_def] >>
  drule_all find_invoke_site_lookup >> strip_tac >> gvs[] >>
  `bb_well_formed bb` by
    metis_tac[wf_function_def, lookup_block_MEM] >>
  metis_tac[invoke_before_terminator]
QED

Theorem inline_edge_terminator_index:
  bb_well_formed bb /\ get_instruction bb j = SOME inst /\
  is_terminator inst.inst_opcode ==>
  j = LENGTH bb.bb_instructions - 1
Proof
  gvs[get_instruction_def, bb_well_formed_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem inline_keep_edge_predecessor:
  inline_cell_frame (KeepCell e) c d /\ wf_function c.ic_function /\
  lookup_block c.ic_block c.ic_function.fn_blocks = SOME sb /\
  get_instruction sb c.ic_index = SOME src /\
  is_terminator src.inst_opcode /\ MEM dest (bb_succs sb) ==>
  inline_phi_entry_step (InlineKeep e) (dest,SOME c.ic_block) =
    (dest,SOME d.ic_block)
Proof
  strip_tac >>
  `bb_well_formed sb` by metis_tac[wf_function_def, lookup_block_MEM] >>
  drule_all inline_edge_terminator_index >> strip_tac >>
  gvs[inline_cell_frame_def, inline_make_cell_def] >>
  drule_all inline_edge_site_shape >> strip_tac >>
  drule inline_phi_entry_keep_some >>
  disch_then (qspecl_then [`c.ic_block`, `dest`] mp_tac) >>
  Cases_on `c.ic_block = e.ise_block` >> gvs[] >>
  simp[inline_return_succs]
QED

Theorem inline_enter_edge_predecessor:
  inline_cell_frame (EnterCell e k) c d ==>
  inline_phi_entry_step (InlineEnter e) (dest,SOME c.ic_block) =
    (STRCAT e.ise_prefix dest,SOME d.ic_block)
Proof
  simp[inline_cell_frame_def, inline_make_cell_def, inline_phi_entry_step_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem inline_edge_cell_successors:
  wf_function c.ic_function /\ inline_cell_at c /\
  c.ic_fields = inline_inst_fields src /\ is_terminator src.inst_opcode ==>
  ?bb inst. lookup_block c.ic_block c.ic_function.fn_blocks = SOME bb /\
    get_instruction bb c.ic_index = SOME inst /\
    inline_inst_fields inst = inline_inst_fields src /\
    bb_succs bb = nub (REVERSE (get_successors src))
Proof
  simp[inline_cell_at_def, inline_fetched_fields_def] >> rpt strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def, lookup_block_MEM] >>
  `inst = LAST bb.bb_instructions` by
    (irule simplifyCfgStructTheory.bb_well_formed_terminator_last >>
     gvs[get_instruction_def, inline_inst_fields_def] >>
     metis_tac[MEM_EL]) >>
  qexistsl [`bb`, `inst`] >> simp[] >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  Cases_on `bb.bb_instructions` >>
  gvs[bb_succs_def, get_successors_def, inline_inst_fields_def]
QED

Theorem inline_edge_frame:
  inline_cell_frame tag c d /\ wf_function c.ic_function /\
  c.ic_fields = inline_inst_fields src /\
  MEM src.inst_opcode [JMP; JNZ; DJMP] /\
  MEM dest (get_successors src) /\ (!e. tag <> SelectedJump e) ==>
  ?dst. d.ic_fields = inline_inst_fields dst /\
    MEM dst.inst_opcode [JMP; JNZ; DJMP] /\
    MEM (inline_choice_rename (inline_cell_choice tag) dest) (get_successors dst) /\
    inline_phi_entry_step (inline_cell_choice tag) (dest,SOME c.ic_block) =
      (inline_choice_rename (inline_cell_choice tag) dest,SOME d.ic_block)
Proof
  strip_tac >>
  `inline_cell_at c` by metis_tac[inline_cell_frame_source] >>
  `is_terminator src.inst_opcode /\
   ~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP]` by
    gvs[MEM, is_terminator_def] >>
  drule_all inline_edge_cell_successors >> strip_tac >>
  `MEM dest (bb_succs bb)` by simp[] >>
  `MEM dest (fn_labels c.ic_function)` by
    metis_tac[wf_function_def, fn_succs_closed_def, lookup_block_MEM] >>
  drule_all inline_cell_frame_ordinary_fields >> strip_tac >>
  Cases_on `tag` >> simp[inline_cell_choice_def, inline_choice_rename_def]
  >- (qexists `src` >> simp[] >>
      conj_tac >- gvs[] >>
      irule inline_keep_edge_predecessor >> simp[] >>
      gvs[inline_inst_fields_def])
  >- metis_tac[] >>
  rename1 `inline_cell_frame (EnterCell e k) c d` >>
  qexists `clone_instruction e.ise_prefix (fn_labels e.ise_callee) src` >>
  simp[clone_instruction_successors, clone_instruction_def] >>
  `c.ic_function = e.ise_callee` by gvs[inline_cell_frame_def] >>
  conj_tac >- gvs[] >>
  conj_tac >- (simp[MEM_MAP] >> qexists `dest` >> simp[] >> metis_tac[]) >>
  irule inline_enter_edge_predecessor >> qexists `k` >> simp[]
QED

Theorem inline_edge_zipper_predecessor:
  !frames c d src dest.
  inline_cell_zipper c frames d /\ wf_function c.ic_function /\
  EVERY (\(tag,next). wf_function next.ic_function) frames /\
  c.ic_fields = inline_inst_fields src /\
  MEM src.inst_opcode [JMP; JNZ; DJMP] /\ MEM dest (get_successors src) /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  inline_phi_entry_path (MAP (\(tag,next). inline_cell_choice tag) frames)
    (dest,SOME c.ic_block) =
    (inline_path_rename (MAP (\(tag,next). inline_cell_choice tag) frames) dest,
     SOME d.ic_block)
Proof
  Induct >- simp[inline_cell_zipper_def, inline_phi_entry_path_def,
                 inline_path_rename_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[inline_cell_zipper_def] >> strip_tac >>
  drule inline_edge_frame >>
  disch_then (qspecl_then [`src`, `dest`] mp_tac) >> simp[] >> strip_tac >>
  once_rewrite_tac[inline_phi_entry_path_def] >>
  pure_once_rewrite_tac[FOLDL] >>
  simp[GSYM inline_phi_entry_path_def,
       inline_path_rename_def, combinTheory.o_DEF] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem inline_edge_edit_wf:
  inline_site_edit_valid e /\
  qualified_origin C e.ise_state.is_inline_count e.ise_caller /\
  qualified_origin C e.ise_state.is_inline_count e.ise_callee ==>
  wf_function e.ise_final
Proof
  strip_tac >>
  `inliner_fn_origin C e.ise_state.is_inline_count e.ise_caller /\
   inliner_fn_origin C e.ise_state.is_inline_count e.ise_callee` by
    metis_tac[functionInlinerOriginTheory.qualified_origin_erasure] >>
  drule functionInlinerOriginTheory.inliner_fn_origin_structure >> strip_tac >>
  rev_drule functionInlinerOriginTheory.inliner_fn_origin_structure >> strip_tac >>
  qpat_x_assum `inline_site_edit_valid e`
    (strip_assume_tac o REWRITE_RULE [inline_site_edit_valid_def]) >>
  drule_all inline_one_site_structure >> simp[]
QED

Theorem inline_edge_zipper_wf:
  inline_annotated_origin C n root cert /\
  inline_routed_leaf cert root p c.ic_function
    (MAP (\(tag,next). inline_cell_choice tag) frames) /\
  inline_cell_zipper c frames d ==>
  EVERY (\(tag,next). wf_function next.ic_function) frames
Proof
  strip_tac >> drule inline_routed_leaf_producer_origins >>
  disch_then (drule_then assume_tac) >>
  qpat_x_assum `inline_routed_leaf _ _ _ _ _` kall_tac >>
  qpat_x_assum `inline_annotated_origin _ _ _ _` kall_tac >>
  qpat_x_assum `inline_cell_zipper _ _ _` mp_tac >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  qid_spec_tac `c` >> qid_spec_tac `d` >> Induct_on `frames` >>
  simp[inline_cell_zipper_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >>
  simp[inline_cell_zipper_def] >> strip_tac >> strip_tac >>
  conj_tac >-
    (Cases_on `h0` >> gvs[inline_cell_choice_def, inline_cell_frame_def,
       inline_make_cell_def] >> metis_tac[inline_edge_edit_wf]) >>
  first_x_assum irule >> metis_tac[]
QED

(* Both JNZ outcomes and every successful DJMP are covered by the actual
   step's successor witness, rather than by an arbitrary destination label. *)
Theorem inline_actual_branch_phi_edge:
  inline_annotated_origin C0 n root cert /\
  inline_routed_leaf cert root p c.ic_function
    (MAP (\(tag,next). inline_cell_choice tag) frames) /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  wf_function c.ic_function /\
  c.ic_fields = inline_inst_fields src /\
  MEM src.inst_opcode [JMP; JNZ; DJMP] /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  s.vs_current_bb = c.ic_block /\ t.vs_current_bb = d.ic_block /\
  t.vs_inst_idx = d.ic_index /\ ~s.vs_halted /\
  (!op w. MEM op src.inst_operands /\ eval_operand op s = SOME w ==>
    eval_operand (inline_rename_operand (inline_cell_var_action frames)
      (inline_cell_label_action frames) op) t = SOME w) /\
  step_inst fuel C src s = OK u ==>
  ?bb dst source_entry target_entry v.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME dst /\
    step_inst tfuel Tctx dst t = OK v /\
    lookup_block u.vs_current_bb c.ic_function.fn_blocks = SOME source_entry /\
    lookup_block v.vs_current_bb root.fn_blocks = SOME target_entry /\
    (!q. u.vs_prev_bb = SOME q ==> MEM q (fn_labels c.ic_function)) /\
    (v.vs_current_bb,v.vs_prev_bb) =
      inline_phi_entry_path (MAP (\(tag,next). inline_cell_choice tag) frames)
        (u.vs_current_bb,u.vs_prev_bb)
Proof
  strip_tac >>
  `~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
   src.inst_opcode <> INVOKE /\ is_terminator src.inst_opcode` by
    gvs[MEM, is_terminator_def] >>
  drule_all inline_cell_zipper_mapped_fields >> strip_tac >>
  drule_all inline_cell_zipper_sound >>
  simp[inline_cell_at_def, inline_fetched_fields_def] >> strip_tac >>
  rename1 `get_instruction bb d.ic_index = SOME dst` >>
  `dst.inst_opcode = src.inst_opcode /\
   dst.inst_operands = MAP (inline_rename_operand (inline_cell_var_action frames)
     (inline_cell_label_action frames)) src.inst_operands` by
    gvs[inline_inst_fields_def] >>
  drule_all inline_branch_success_step >>
  disch_then (qspecl_then [`tfuel`, `Tctx`] strip_assume_tac) >>
  `~u.vs_halted` by
    (qpat_x_assum `u = jump_to _ _` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >>
     simp[jump_to_def]) >>
  `MEM u.vs_current_bb (get_successors src)` by
    (irule venomExecProofsTheory.step_inst_base_term_succs >>
     simp[] >> qexists_tac `s` >>
     metis_tac[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  `u.vs_prev_bb = SOME c.ic_block` by
    (qpat_x_assum `u = jump_to _ _` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\s:venom_state. s.vs_prev_bb``) >>
     simp[jump_to_def]) >>
  drule_all inline_edge_cell_successors >> strip_tac >>
  `MEM u.vs_current_bb (fn_labels c.ic_function)` by
    metis_tac[wf_function_def, fn_succs_closed_def, lookup_block_MEM, MEM_nub,
      MEM_REVERSE] >>
  `?entry. lookup_block u.vs_current_bb c.ic_function.fn_blocks = SOME entry` by
    (qpat_x_assum `MEM _ (fn_labels _)` mp_tac >>
     rewrite_tac[fn_labels_def] >>
     disch_then (strip_assume_tac o MATCH_MP dfAnalyzeProofsTheory.lookup_block_exists) >>
     goal_assum (drule_at Any)) >>
  drule_all inline_edge_zipper_wf >> strip_tac >>
  drule_all inline_edge_zipper_predecessor >> strip_tac >>
  drule_all inline_cell_zipper_entry_label >> strip_tac >>
  drule_all inline_cell_routed_before_phi >>
  disch_then (qspec_then `0` strip_assume_tac) >>
  qexistsl [`bb`, `dst`, `entry`, `tb`,
    `jump_to (inline_cell_label_action frames u.vs_current_bb) t`] >>
  simp[jump_to_def] >>
  conj_tac >- metis_tac[lookup_block_MEM, lookup_block_label, fn_labels_def, MEM_MAP] >>
  qpat_x_assum `inline_phi_entry_path _ _ = _` mp_tac >>
  simp[jump_to_def] >>
  metis_tac[lookup_block_MEM, lookup_block_label, fn_labels_def, MEM_MAP]
QED

(* A generated continuation is a body cut, not a source predecessor edge. *)
Theorem inline_generated_continuation_phi_cut:
  inline_site_edit_valid e /\ wf_function e.ise_caller /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb ==>
  ?rb. lookup_block e.ise_return e.ise_final.fn_blocks = SOME rb /\
    MAP inline_inst_fields rb.bb_instructions =
      MAP inline_inst_fields (DROP (e.ise_index+1) bb.bb_instructions) /\
    phi_prefix_length rb.bb_instructions = 0 /\
    (!v. eval_phis v rb.bb_instructions = OK v) /\
    (!v k ctx. v.vs_current_bb = e.ise_return ==>
      run_blocks (SUC k) ctx e.ise_final v =
        case exec_block k ctx rb (v with vs_inst_idx := 0) of
          OK w => if w.vs_halted then Halt w else run_blocks k ctx e.ise_final w
        | IntRet ir w => IntRet ir w
        | other => other)
Proof
  strip_tac >> drule_all inline_edge_site_shape >> strip_tac >>
  irule functionInlinerSimulationTheory.inline_final_return_dispatch >>
  simp[] >>
  qexistsl [`e.ise_callee`, `e.ise_caller`, `e.ise_state`, `e.ise_next`,
    `e.ise_block`] >>
  gvs[inline_site_edit_valid_def]
QED
