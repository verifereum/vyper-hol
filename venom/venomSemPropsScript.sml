(*
 * Venom Semantic Properties
 *
 * General semantic lemmas useful for any optimization pass.
 * Contains properties of bool_to_word and instruction behavior lemmas.
 *)

Theory venomSemProps
Ancestors
  venomSem venomInst venomState

(* ==========================================================================
   bool_to_word Properties

   WHY THESE ARE TRUE: bool_to_word is defined as:
     bool_to_word T = 1w
     bool_to_word F = 0w
   So bool_to_word b = 0w iff b = F iff ~b.
   ========================================================================== *)

Theorem bool_to_word_T:
  bool_to_word T = 1w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_F:
  bool_to_word F = 0w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_eq_0w:
  (bool_to_word b = 0w) <=> ~b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

Theorem bool_to_word_neq_0w:
  (bool_to_word b <> 0w) <=> b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

(* ==========================================================================
   Instruction Behavior Lemmas
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, ISZERO uses exec_unop with
   (\x. bool_to_word (x = 0w)). exec_unop evaluates the single operand,
   applies the function, and updates the output variable. *)
Theorem step_iszero_value:
  !s cond_op out id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  rw[step_inst_def, exec_unop_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, ASSERT evaluates its operand.
   If cond = 0w, it returns Revert (revert_state s).
   If cond <> 0w, it returns OK s. *)
Theorem step_assert_behavior:
  !s cond_op id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then Revert (revert_state s) else OK s
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, REVERT unconditionally returns
   Revert (revert_state s) regardless of operands. *)
Theorem step_revert_always_reverts:
  !inst s.
    inst.inst_opcode = REVERT ==>
    step_inst inst s = Revert (revert_state s)
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, JMP unconditionally jumps to the label. *)
Theorem step_jmp_behavior:
  !s lbl id.
    step_inst <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, JNZ evaluates the condition.
   If cond <> 0w, it jumps to if_nonzero; else to if_zero. *)
Theorem step_jnz_behavior:
  !s cond_op if_nonzero if_zero id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  rw[step_inst_def]
QED

(* ===== Non-terminator control fields ===== *)

Theorem step_inst_preserves_prev_bb:
  !inst s s'.
    step_inst inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_binop_def, exec_unop_def, exec_modop_def] >>
  gvs[AllCaseEqs()] >>
  fs[update_var_def, mstore_def, sstore_def, tstore_def,
     write_memory_with_expansion_def]
QED

Theorem step_inst_preserves_current_bb:
  !inst s s'.
    step_inst inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_current_bb = s.vs_current_bb
Proof
  rw[step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >>
  fs[exec_binop_def, exec_unop_def, exec_modop_def] >>
  gvs[AllCaseEqs()] >>
  fs[update_var_def, mstore_def, sstore_def, tstore_def,
     write_memory_with_expansion_def]
QED

Theorem step_in_block_preserves_prev_bb:
  !bb s s' is_term.
    step_in_block bb s = (OK s', is_term) /\
    ~is_term ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  gvs[AllCaseEqs()] >>
  drule_all step_inst_preserves_prev_bb >>
  simp[next_inst_def]
QED

Theorem step_in_block_preserves_current_bb:
  !bb s s' is_term.
    step_in_block bb s = (OK s', is_term) /\
    ~is_term ==>
    s'.vs_current_bb = s.vs_current_bb
Proof
  rw[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  gvs[AllCaseEqs()] >>
  drule_all step_inst_preserves_current_bb >>
  simp[next_inst_def]
QED

Theorem step_inst_terminator_sets_prev_bb:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst inst s = OK s' /\
    ~s'.vs_halted ==>
    s'.vs_prev_bb <> NONE
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  qpat_x_assum `is_terminator _` mp_tac >>
  simp[step_inst_def] >>
  (* Only JMP/JNZ give OK without halting, both use jump_to *)
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[AllCaseEqs(), jump_to_def]
QED

Theorem step_inst_terminator_prev_bb:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst inst s = OK s' /\
    ~s'.vs_halted ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  qpat_x_assum `is_terminator _` mp_tac >>
  simp[step_inst_def] >>
  (* Only JMP/JNZ give OK without halting, both use jump_to *)
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >> gvs[AllCaseEqs(), jump_to_def]
QED

Theorem step_inst_terminator_successor:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst inst s = OK s' /\
    ~s'.vs_halted ==>
    MEM s'.vs_current_bb (get_successors inst)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  qpat_x_assum `is_terminator _` mp_tac >>
  simp[step_inst_def, get_successors_def] >>
  Cases_on `inst.inst_opcode` >> simp[is_terminator_def] >>
  strip_tac >>
  gvs[AllCaseEqs(), jump_to_def, get_label_def] >>
  Cases_on `get_label cond_op` >> simp[]
QED

Theorem run_block_ok_not_halted_sets_prev_bb:
  !bb s s'.
    run_block bb s = OK s' /\ ~s'.vs_halted ==>
    s'.vs_prev_bb <> NONE
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  qpat_x_assum `run_block _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  Cases_on `r` >> simp[] >- (
    (* Terminal case *)
    spose_not_then strip_assume_tac >> gvs[] >>
    qpat_x_assum `step_in_block _ _ = _` mp_tac >> simp[step_in_block_def] >>
    Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
    Cases_on `step_inst x s` >> simp[] >>
    Cases_on `is_terminator x.inst_opcode` >> simp[] >>
    spose_not_then strip_assume_tac >> gvs[] >>
    drule_at (Pos last) step_inst_terminator_sets_prev_bb >> simp[] >>
    qexists_tac `x` >> qexists_tac `s` >> simp[]
  ) >>
  (* Non-terminal case: use IH *)
  spose_not_then strip_assume_tac >> gvs[] >>
  first_x_assum (qspecl_then [`OK v`, `F`, `v`] mp_tac) >> simp[]
QED

Theorem run_block_ok_prev_bb:
  !bb s s'.
    run_block bb s = OK s' /\ ~s'.vs_halted ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  qpat_x_assum `run_block _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s` >> Cases_on `q` >> simp[] >>
  Cases_on `v.vs_halted` >> simp[] >>
  Cases_on `r` >> simp[]
  >- (
    (* Terminal case *)
    qpat_x_assum `step_in_block _ _ = _` mp_tac >>
    simp[step_in_block_def] >>
    Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
    gvs[AllCaseEqs()] >>
    strip_tac >> gvs[] >>
    metis_tac[step_inst_terminator_prev_bb]
  )
  >- (
    (* Non-terminal case: use IH *)
    `v.vs_current_bb = s.vs_current_bb` by (
      qspecl_then [`bb`, `s`, `v`, `F`] mp_tac
        step_in_block_preserves_current_bb >>
      simp[]
    ) >>
    first_x_assum (qspecl_then [`OK v`, `F`, `v`] mp_tac) >> simp[]
  )
QED
