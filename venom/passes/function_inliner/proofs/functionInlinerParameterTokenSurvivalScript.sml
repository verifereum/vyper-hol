(* Surviving opaque tokens retain their syntax, not their token value. *)
Theory functionInlinerParameterTokenSurvival
Ancestors
  functionInlinerTokenLineage functionInlinerReachableCuts
  functionInlinerLocation functionInlinerSiteSimulation functionInlinerSiteLayout functionInlinerDefs
  venomExecSemantics venomInst list rich_list

Theorem inline_token_frame_survivor_shape:
  inline_cell_frame tag c d /\
  c.ic_fields = (RETPC_PARAM,[Lit idx],[x]) /\
  (!e. tag <> SelectedJump e) /\ FST d.ic_fields = RETPC_PARAM ==>
  d.ic_fields = (RETPC_PARAM,[Lit idx],
    [case tag of EnterCell e k => STRCAT e.ise_prefix x | _ => x])
Proof
  Cases_on `tag` >> simp[inline_cell_frame_def] >> rpt strip_tac >>
  gvs[inline_make_cell_def, inline_inst_fields_def, inline_edit_repair_def]
  >> gvs[inline_cell_focus_def, rewrite_inline_inst_def, clone_instruction_def,
      is_param_opcode_def, get_instruction_def] >>
  Cases_on `SND (inline_cell_prefix i bb cb c.ic_index) <
    LENGTH (rotate_invoke_ops (EL i.ise_index bb.bb_instructions).inst_operands)` >>
  gvs[inline_make_cell_def, inline_inst_fields_def, inline_edit_repair_def] >>
  qpat_x_assum `[Lit idx] = _` (SUBST1_TAC o SYM) >>
  simp[clone_operand_def]
QED

Theorem inline_assign_zipper_opcode:
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  FST c.ic_fields = ASSIGN /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
  FST d.ic_fields = ASSIGN
Proof
  simp[inline_cell_at_def, inline_fetched_fields_def] >> rpt strip_tac >>
  `c.ic_fields = inline_inst_fields inst` by metis_tac[] >>
  `inst.inst_opcode = ASSIGN` by
    (qpat_x_assum `FST c.ic_fields = ASSIGN` mp_tac >>
     gvs[inline_inst_fields_def]) >>
  `~MEM inst.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP]`
    by simp[] >>
  drule_all inline_cell_zipper_mapped_fields >>
  simp[inline_inst_fields_def]
QED

Theorem inline_token_zipper_survivor_shape:
  !frames c d idx x.
  inline_cell_zipper c frames d /\
  c.ic_fields = (RETPC_PARAM,[Lit idx],[x]) /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  FST d.ic_fields = RETPC_PARAM ==>
  d.ic_fields = (RETPC_PARAM,[Lit idx],[inline_cell_var_action frames x])
Proof
  Induct >> simp[inline_cell_zipper_def, inline_cell_var_action_def] >>
  Cases_on `h` >> simp[inline_cell_zipper_def, inline_cell_var_action_def] >>
  rpt strip_tac >>
  `FST c.ic_fields = RETPC_PARAM` by simp[] >>
  `FST r.ic_fields = RETPC_PARAM` by
    (drule_all inline_token_frame_cases >> simp[] >> strip_tac >>
     gvs[inline_token_consumes_def] >>
     `inline_cell_at r` by metis_tac[inline_cell_frame_sound] >>
     `FST r.ic_fields = ASSIGN` by simp[] >>
     drule_all inline_assign_zipper_opcode >> simp[]) >>
  drule_all inline_token_frame_survivor_shape >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED

Theorem inline_token_zipper_survivor_step:
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = (RETPC_PARAM,[Lit idx],[x]) /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  FST d.ic_fields = RETPC_PARAM ==>
  ?bb inst.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME inst /\
    inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
    inst.inst_outputs = [inline_cell_var_action frames x] /\
    step_inst fuel ctx inst t =
      OK (update_var (inline_cell_var_action frames x) t.vs_return_pc_token t)
Proof
  strip_tac >> drule_all inline_token_zipper_survivor_shape >> strip_tac >>
  drule_all inline_cell_zipper_sound >>
  simp[inline_cell_at_def, inline_fetched_fields_def] >> rpt strip_tac >>
  gvs[inline_inst_fields_def] >>
  irule functionInlinerOperationalTheory.inline_token_step >> simp[]
QED
