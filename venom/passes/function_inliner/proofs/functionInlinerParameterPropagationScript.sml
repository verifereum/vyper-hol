(* Emitted assignments persist along valid annotated compiler edit paths. *)
Theory functionInlinerParameterPropagation
Ancestors
  functionInlinerSelectedParameters functionInlinerParameterLineage
  functionInlinerReachableCuts functionInlinerOccurrences
  functionInlinerActivation functionInlinerLocation functionInlinerDefs
  functionInlinerFrame functionInlinerSiteLayout
  functionInlinerRoutedProvenance functionInlinerWf venomInst list rich_list combin

Definition inline_annotated_choice_path_def:
  (inline_annotated_choice_path ctx [] fn root <=> root = fn) /\
  (inline_annotated_choice_path ctx (choice::rest) fn root <=>
    ?e a b.
      inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
      inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
      inline_site_edit_valid e /\
      ((choice = InlineKeep e /\ fn = e.ise_caller) \/
       (choice = InlineEnter e /\ fn = e.ise_callee)) /\
      inline_annotated_choice_path ctx rest e.ise_final root)
End

Theorem inline_assign_keep_produce:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
  inline_cell_at c /\ c.ic_fields = (ASSIGN,ops,outs) ==>
  ?d. inline_cell_frame (KeepCell e) c d /\
      d.ic_function = e.ise_final /\ inline_cell_at d /\
      d.ic_fields = (ASSIGN,ops,outs)
Proof
  strip_tac >> drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `ALL_DISTINCT (fn_labels e.ise_caller)` by
    metis_tac[inline_annotated_origin_labels] >>
  `?source. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source /\
    e.ise_index < LENGTH source.bb_instructions /\
    (EL e.ise_index source.bb_instructions).inst_opcode = INVOKE` by
    metis_tac[inline_site_edit_valid_def, find_invoke_site_lookup] >>
  `c.ic_block <> e.ise_block \/ c.ic_index <> e.ise_index` by
    (gvs[inline_cell_at_def, inline_fetched_fields_def, get_instruction_def,
         inline_inst_fields_def] >> rpt strip_tac >> gvs[]) >>
  `?d. inline_cell_frame (KeepCell e) c d` by
    metis_tac[inline_keep_cell_produce] >>
  qexists `d` >> simp[] >>
  `inline_cell_at d` by metis_tac[inline_cell_frame_sound] >> simp[] >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[inline_cell_frame_def] >> rpt strip_tac >>
  gvs[inline_make_cell_def, inline_inst_fields_def, inline_edit_repair_def]
QED

Theorem inline_assign_enter_produce:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ c.ic_function = e.ise_callee /\
  inline_cell_at c /\ c.ic_fields = (ASSIGN,ops,outs) ==>
  ?d. inline_cell_frame (EnterCell e 0) c d /\
      d.ic_function = e.ise_final /\ inline_cell_at d /\
      d.ic_fields = (ASSIGN,
        MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops,
        MAP (STRCAT e.ise_prefix) outs)
Proof
  strip_tac >> drule_all inline_annotated_edit_fetch_facts >> strip_tac >>
  `?cb inst. lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb c.ic_index = SOME inst /\
    inline_inst_fields inst = (ASSIGN,ops,outs)` by
    metis_tac[inline_cell_at_def, inline_fetched_fields_def] >>
  `MEM c.ic_block (fn_labels e.ise_callee)` by
    (simp[fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  `inline_cell_focus e bb cb c.ic_index =
    ([clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst],
     SND (inline_cell_prefix e bb cb c.ic_index))` by
    gvs[inline_cell_focus_def, get_instruction_def, inline_inst_fields_def,
        clone_instruction_def, rewrite_inline_inst_def, is_param_opcode_def] >>
  `?d. inline_cell_frame (EnterCell e 0) c d` by
    (irule inline_enter_cell_produce >> simp[] >> metis_tac[]) >>
  qexists `d` >> simp[] >>
  `inline_cell_at d` by metis_tac[inline_cell_frame_sound] >> simp[] >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[inline_cell_frame_def] >> rpt strip_tac >>
  gvs[inline_make_cell_def, inline_inst_fields_def, inline_edit_repair_def,
      clone_instruction_def] >> metis_tac[]
QED

Theorem inline_assign_path_produce:
  !path c ops outs root.
  inline_annotated_choice_path ctx path c.ic_function root /\
  inline_cell_at c /\ c.ic_fields = (ASSIGN,ops,outs) ==>
  ?frames d.
    inline_cell_zipper c frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = path /\
    d.ic_function = root /\ inline_cell_at d /\
    d.ic_fields = (ASSIGN,
      FOLDL (\ops choice. case choice of
        InlineKeep e => ops
      | InlineEnter e => MAP (clone_operand e.ise_prefix (fn_labels e.ise_callee)) ops)
        ops path,
      MAP (inline_path_rename path) outs)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`[]`, `c`] >>
      gvs[inline_annotated_choice_path_def, inline_cell_zipper_def,
          inline_path_rename_def]) >>
  qpat_x_assum `inline_annotated_choice_path _ _ _ _` mp_tac >>
  simp[inline_annotated_choice_path_def] >> strip_tac >> gvs[]
  >- (drule_all inline_assign_keep_produce >> strip_tac >>
      first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
      disch_then (qspec_then `root` mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [`(KeepCell e,d)::frames`, `d'`] >>
      simp[inline_cell_zipper_def, inline_cell_choice_def,
           inline_path_rename_def, inline_choice_rename_def, o_DEF, SF ETA_ss]) >>
  drule_all inline_assign_enter_produce >> strip_tac >>
  first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
      disch_then (qspec_then `root` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`(EnterCell e 0,d)::frames`, `d'`] >>
  simp[inline_cell_zipper_def, inline_cell_choice_def,
       inline_path_rename_def, inline_choice_rename_def, MAP_MAP_o, o_DEF]
QED
