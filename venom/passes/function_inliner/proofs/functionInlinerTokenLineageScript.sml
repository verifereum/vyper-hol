(* Opaque RETPC tokens follow their actual CURRENT rewrite counter. *)
Theory functionInlinerTokenLineage
Ancestors
  functionInlinerReachableCuts functionInlinerSiteSimulation
  functionInlinerLocation functionInlinerSiteLayout functionInlinerDefs venomInst list rich_list

Theorem inline_token_keep_survives:
  inline_cell_frame (KeepCell e) c d /\
  FST c.ic_fields = RETPC_PARAM ==>
  FST d.ic_fields = RETPC_PARAM
Proof
  simp[inline_cell_frame_def] >> rpt strip_tac >>
  gvs[inline_make_cell_def, inline_inst_fields_def, inline_edit_repair_def]
QED

Theorem inline_token_enter_cases:
  inline_cell_frame (EnterCell e k) c d /\
  FST c.ic_fields = RETPC_PARAM ==>
  FST d.ic_fields = RETPC_PARAM \/
  (k = 0 /\ ?bb cb h.
    lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
    lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
    h = SND (inline_cell_prefix e bb cb c.ic_index) /\
    h < LENGTH (rotate_invoke_ops
      (EL e.ise_index bb.bb_instructions).inst_operands) /\
    d.ic_fields =
      (ASSIGN, [EL h (rotate_invoke_ops
        (EL e.ise_index bb.bb_instructions).inst_operands)],
       MAP (STRCAT e.ise_prefix) (SND (SND c.ic_fields))))
Proof
  simp[inline_cell_frame_def] >> rpt strip_tac >>
  gvs[inline_inst_fields_def, get_instruction_def] >>
  gvs[inline_cell_focus_def, rewrite_inline_inst_def, clone_instruction_def,
      is_param_opcode_def] >>
  Cases_on `SND (inline_cell_prefix e bb cb c.ic_index) <
    LENGTH (rotate_invoke_ops (EL e.ise_index bb.bb_instructions).inst_operands)` >>
  gvs[inline_make_cell_def, inline_edit_repair_def, inline_inst_fields_def] >>
  metis_tac[]
QED

(* The consuming edit owns this argument index; it need not be the edit
   that originally selected the activation containing the token. *)
Definition inline_token_consumes_def:
  inline_token_consumes e c d <=>
    ?bb cb h.
      lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
      lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
      h = SND (inline_cell_prefix e bb cb c.ic_index) /\
      h < LENGTH (rotate_invoke_ops
        (EL e.ise_index bb.bb_instructions).inst_operands) /\
      d.ic_fields =
        (ASSIGN, [EL h (rotate_invoke_ops
          (EL e.ise_index bb.bb_instructions).inst_operands)],
         MAP (STRCAT e.ise_prefix) (SND (SND c.ic_fields)))
End

Theorem inline_token_frame_cases:
  inline_cell_frame tag c d /\ FST c.ic_fields = RETPC_PARAM /\
  (!e. tag <> SelectedJump e) ==>
  FST d.ic_fields = RETPC_PARAM \/
  ?e. tag = EnterCell e 0 /\ inline_token_consumes e c d
Proof
  Cases_on `tag` >> simp[] >> rpt strip_tac
  >- metis_tac[inline_token_keep_survives] >>
  drule_all inline_token_enter_cases >>
  simp[inline_token_consumes_def] >> metis_tac[]
QED

Theorem inline_token_zipper_first_consumption:
  !frames c d.
    inline_cell_zipper c frames d /\ FST c.ic_fields = RETPC_PARAM /\
    EVERY (\(tag,next). !e. tag <> SelectedJump e) frames ==>
    FST d.ic_fields = RETPC_PARAM \/
    ?before e incoming next after.
      frames = before ++ [(EnterCell e 0,next)] ++ after /\
      inline_cell_zipper c before incoming /\
      FST incoming.ic_fields = RETPC_PARAM /\
      EVERY (\(tag,cell). FST cell.ic_fields = RETPC_PARAM) before /\
      inline_cell_frame (EnterCell e 0) incoming next /\
      inline_token_consumes e incoming next /\
      inline_cell_zipper next after d /\
      inline_cell_at incoming /\ inline_cell_at next
Proof
  Induct >> simp[inline_cell_zipper_def] >>
  Cases_on `h` >> simp[inline_cell_zipper_def] >> rpt strip_tac >>
  drule_all inline_token_frame_cases >> strip_tac
  >- (first_x_assum drule >> simp[] >> strip_tac
      >- simp[] >>
      disj2_tac >>
      qexistsl_tac [`(q,r)::before`, `e`, `incoming`, `next`, `after`] >>
      simp[inline_cell_zipper_def]) >>
  disj2_tac >>
  qexistsl_tac [`[]`, `e`, `c`, `r`, `frames`] >>
  simp[inline_cell_zipper_def] >>
  metis_tac[inline_cell_frame_source, inline_cell_frame_sound]
QED
