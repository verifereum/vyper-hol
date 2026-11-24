(* Interpret the restore observation at the enclosing operand cut. *)
Theory restoreCreateObservation
Ancestors
  restoreSegmentLaws entryCreateAdminSequence entryCreateEncoderSteps
  entryCreatePathScope entryCreateFocusSpec abiEncoderProps fragExec list pair

Theorem restore_segment_laws_create_prefix:
  restore_segment_laws su.cs_next_id sb.cs_next_id
    (sb.cs_current_bb,LENGTH sb.cs_current_insts) explicit ctx fn
    (\s t. create_expr_prefix su sb explicit ctx fn s [] t)
Proof
  rewrite_tac[restore_segment_laws_def] >> BETA_TAC >>
  conj_tac >- simp[] >>
  conj_tac >-
    (rpt strip_tac >>
     drule_all (SIMP_RULE bool_ss [APPEND]
       (Q.INST [`left` |-> `[]`, `right` |-> `[]`] create_expr_prefix_append)) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `EVERY (\i. i.inst_id IN frag_ids su sb /\ i.inst_opcode <> INVOKE /\
                  i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) code` by
        fs[EVERY_MEM, frag_ids_def] >>
      drule_all create_admin_sequence_prefix_run >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `~create_operand_at sb s /\ i.inst_id IN frag_ids su sb` by
    fs[create_operand_at_def, frag_ids_def] >>
  drule_all encoder_window_branch_prefix >> simp[]
QED
