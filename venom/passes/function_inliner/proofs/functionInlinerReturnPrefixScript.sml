(* Returns survive all-Keep paths up to their unique selected Enter. *)
Theory functionInlinerReturnPrefix
Ancestors
  functionInlinerParameterPropagation functionInlinerReachableCuts
  functionInlinerOccurrences functionInlinerLocation functionInlinerSiteLayout
  functionInlinerDefs functionInlinerFrame functionInlinerRoutedProvenance
  functionInlinerActivation functionInlinerWf venomInst list

Theorem inline_return_keep_produce:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
  inline_cell_at c /\ c.ic_fields = (opc,ops,outs) /\
  (opc = RET \/ opc = RETFMP) ==>
  ?d. inline_cell_frame (KeepCell e) c d /\
      d.ic_function = e.ise_final /\ inline_cell_at d /\
      d.ic_fields = c.ic_fields
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

Theorem inline_return_keep_path_produce:
  !path c opc ops outs root.
  inline_annotated_choice_path ctx path c.ic_function root /\
  EVERY (\choice. ?e. choice = InlineKeep e) path /\
  inline_cell_at c /\ c.ic_fields = (opc,ops,outs) /\
  (opc = RET \/ opc = RETFMP) ==>
  ?frames d.
    inline_cell_zipper c frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = path /\
    d.ic_function = root /\ inline_cell_at d /\
    d.ic_fields = (opc,ops,outs) /\
    (!counter. inline_path_location path (SOME (inline_cell_location c counter)) =
      SOME (inline_cell_location d counter))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`[]`, `c`] >>
      gvs[inline_annotated_choice_path_def, inline_cell_zipper_def]) >>
  gvs[] >>
  qpat_x_assum `inline_annotated_choice_path _ _ _ _` mp_tac >>
  simp[inline_annotated_choice_path_def] >> strip_tac >> gvs[] >>
  `?d. inline_cell_frame (KeepCell e) c d /\
       d.ic_function = e.ise_final /\ inline_cell_at d /\
       d.ic_fields = c.ic_fields` by metis_tac[inline_return_keep_produce] >>
  first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
  disch_then (qspec_then `root` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`(KeepCell e,d)::frames`, `d'`] >>
  simp[inline_cell_zipper_def, inline_cell_choice_def] >>
  gen_tac >> drule inline_keep_cell_projection >>
  disch_then (qspec_then `counter` assume_tac) >>
  pure_rewrite_tac[inline_path_location_def, FOLDL, inline_location_step_def] >>
  simp[GSYM inline_path_location_def]
QED

(* The final cursor is shared by prefix and focus calculations at Enter;
   instruction IDs need not be preserved by an earlier PHI-edge repair. *)
Theorem inline_return_keep_prefix_fetch:
  inline_annotated_choice_path ctx path fn mid /\
  EVERY (\choice. ?e. choice = InlineKeep e) path /\
  lookup_block l fn.fn_blocks = SOME bb /\
  get_instruction bb j = SOME inst /\
  (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) ==>
  ?frames d current ret.
    inline_cell_zipper (inline_make_cell fn l j (inline_inst_fields inst)) frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = path /\
    d.ic_function = mid /\ inline_cell_at d /\
    lookup_block d.ic_block mid.fn_blocks = SOME current /\
    get_instruction current d.ic_index = SOME ret /\
    inline_inst_fields ret = inline_inst_fields inst /\
    d.ic_fields = inline_inst_fields inst /\
    (!counter. inline_path_location path
      (SOME (inline_cell_location (inline_make_cell fn l j (inline_inst_fields inst)) counter)) =
      SOME (inline_cell_location d counter))
Proof
  strip_tac >>
  `?frames d.
     inline_cell_zipper (inline_make_cell fn l j (inline_inst_fields inst)) frames d /\
     MAP (\(tag,next). inline_cell_choice tag) frames = path /\
     d.ic_function = mid /\ inline_cell_at d /\
     d.ic_fields = (inst.inst_opcode,inst.inst_operands,inst.inst_outputs) /\
     (!counter. inline_path_location path
       (SOME (inline_cell_location (inline_make_cell fn l j (inline_inst_fields inst)) counter)) =
       SOME (inline_cell_location d counter))` by
    (irule inline_return_keep_path_produce >>
     simp[inline_make_cell_def, inline_inst_fields_def,
          inline_cell_at_def, inline_fetched_fields_def] >>
     metis_tac[inline_inst_fields_def]) >>
  qexistsl_tac [`frames`, `d`] >> simp[] >>
  gvs[inline_cell_at_def, inline_fetched_fields_def, inline_inst_fields_def] >>
  metis_tac[]
QED
