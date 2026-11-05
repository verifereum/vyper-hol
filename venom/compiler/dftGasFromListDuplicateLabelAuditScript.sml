Theory dftGasFromListDuplicateLabelAudit
Ancestors
  dftGasOracleDefs contextRawReachable contextCodegenRel venomExecSemantics
  venomInst venomState finite_map words list

Definition audit_assign_def:
  audit_assign = mk_inst 0 ASSIGN [Lit 0w] ["x"]
End
Definition audit_first_def:
  audit_first = mk_inst 0 GAS [] ["x"]
End
Definition audit_second_def:
  audit_second = mk_inst 1 GAS [] ["y"]
End
Definition audit_marker_def:
  audit_marker = mk_inst 2 STOP [] []
End
Definition audit_blocks_def:
  audit_blocks =
    [<| bb_label := "entry";
        bb_instructions := [audit_assign; audit_second; audit_marker] |>;
     <| bb_label := "entry";
        bb_instructions := [audit_first; audit_second; audit_marker] |>]
End
Definition audit_fn_def:
  audit_fn = mk_raw_function "main" audit_blocks
End
Definition audit_ctx_def:
  audit_ctx = mk_venom_context [audit_fn] (SOME "main")
End
Definition audit_start_def:
  audit_start = (init_venom_state "entry") with vs_gas_readings := [1w;2w]
End
Definition audit_mid_def:
  audit_mid w readings = (update_var "x" w audit_start) with
    <| vs_inst_idx := 1; vs_gas_readings := readings |>
End
Definition audit_end_def:
  audit_end w v readings = (update_var "y" v (audit_mid w readings)) with
    <| vs_inst_idx := 2; vs_gas_readings := TL readings |>
End

Theorem audit_distinct:
  EVERY (\fn. EVERY (\bb. ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions))
                fn.fn_blocks) audit_ctx.ctx_functions
Proof
  EVAL_TAC
QED

Theorem audit_entry_facts:
  audit_ctx.ctx_entry = SOME "main" /\
  lookup_function "main" audit_ctx.ctx_functions = SOME audit_fn /\
  fn_entry_label audit_fn = SOME "entry" /\
  enters_block audit_fn
    (audit_start with <| vs_prev_bb := NONE; vs_current_bb := "entry";
                        vs_inst_idx := 0 |>) audit_start /\
  active_inst audit_fn audit_assign audit_start /\
  active_inst audit_fn audit_first audit_start
Proof
  simp[enters_block_def, active_inst_def, audit_ctx_def, audit_fn_def,
       audit_blocks_def, mk_venom_context_def, mk_raw_function_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem audit_steps:
  step_inst 0 audit_ctx audit_assign audit_start = OK ((audit_mid 0w [1w;2w]) with vs_inst_idx := 0) /\
  step_inst 0 audit_ctx audit_first audit_start = OK ((audit_mid 1w [2w]) with vs_inst_idx := 0)
Proof
  EVAL_TAC
QED

Theorem audit_second_steps:
  step_inst 0 audit_ctx audit_second (audit_mid 0w [1w;2w]) =
    OK ((audit_end 0w 1w [1w;2w]) with vs_inst_idx := 1) /\
  step_inst 0 audit_ctx audit_second (audit_mid 1w [2w]) =
    OK ((audit_end 1w 2w [2w]) with vs_inst_idx := 1)
Proof
  EVAL_TAC
QED

Theorem audit_active:
  (!w readings. active_inst audit_fn audit_second (audit_mid w readings)) /\
  (!w v readings. active_inst audit_fn audit_marker (audit_end w v readings))
Proof
  simp[active_inst_def, audit_fn_def, mk_raw_function_def, audit_blocks_def,
       audit_mid_def, audit_end_def, update_var_def, audit_start_def,
       init_venom_state_def, LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
QED

Theorem audit_indices:
  audit_start.vs_inst_idx = 0 /\
  (!w readings. (audit_mid w readings).vs_inst_idx = 1) /\
  (!w v readings. (audit_end w v readings).vs_inst_idx = 2) /\
  (!w readings. (audit_mid w readings) with vs_inst_idx := 1 = audit_mid w readings) /\
  (!w v readings. (audit_end w v readings) with vs_inst_idx := 2 = audit_end w v readings) /\
  ~is_terminator audit_assign.inst_opcode /\
  ~is_terminator audit_first.inst_opcode /\
  ~is_terminator audit_second.inst_opcode
Proof
  simp[audit_start_def, init_venom_state_def, audit_mid_def, audit_end_def,
       audit_assign_def, audit_first_def, audit_second_def, mk_inst_def,
       is_terminator_def]
QED

Theorem audit_raw_entry:
  raw_reachable audit_start audit_ctx audit_fn audit_assign audit_start /\
  raw_reachable audit_start audit_ctx audit_fn audit_first audit_start
Proof
  conj_tac >> irule (cj 1 raw_reachable_rules) >>
  metis_tac[audit_entry_facts]
QED

Theorem audit_raw_next[local]:
  raw_reachable vs0 ctx fn inst s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
  t = (s' with vs_inst_idx := SUC s.vs_inst_idx) /\
  active_inst fn inst' t ==>
  raw_reachable vs0 ctx fn inst' t
Proof
  metis_tac[raw_reachable_rules]
QED

Theorem audit_raw_mid:
  raw_reachable audit_start audit_ctx audit_fn audit_second (audit_mid 0w [1w;2w]) /\
  raw_reachable audit_start audit_ctx audit_fn audit_second (audit_mid 1w [2w])
Proof
  conj_tac
  >- (irule audit_raw_next >> simp[audit_active] >>
      qexistsl_tac [`0`, `audit_assign`, `audit_start`,
        `(audit_mid 0w [1w;2w]) with vs_inst_idx := 0`] >>
      simp[audit_raw_entry, audit_entry_facts, audit_steps, audit_indices]) >>
  irule audit_raw_next >> simp[audit_active] >>
  qexistsl_tac [`0`, `audit_first`, `audit_start`,
    `(audit_mid 1w [2w]) with vs_inst_idx := 0`] >>
  simp[audit_raw_entry, audit_entry_facts, audit_steps, audit_indices]
QED

Theorem audit_raw_end:
  raw_reachable audit_start audit_ctx audit_fn audit_marker (audit_end 0w 1w [1w;2w]) /\
  raw_reachable audit_start audit_ctx audit_fn audit_marker (audit_end 1w 2w [2w])
Proof
  conj_tac
  >- (irule audit_raw_next >> simp[audit_active] >>
      qexistsl_tac [`0`, `audit_second`, `audit_mid 0w [1w;2w]`,
        `(audit_end 0w 1w [1w;2w]) with vs_inst_idx := 1`] >>
      simp[audit_raw_mid, audit_active, audit_second_steps, audit_indices]) >>
  irule audit_raw_next >> simp[audit_active] >>
  qexistsl_tac [`0`, `audit_second`, `audit_mid 1w [2w]`,
    `(audit_end 1w 2w [2w]) with vs_inst_idx := 1`] >>
  simp[audit_raw_mid, audit_active, audit_second_steps, audit_indices]
QED

Theorem audit_values:
  lookup_var "y" (audit_end 0w 1w [1w;2w]) = SOME 1w /\
  lookup_var "y" (audit_end 1w 2w [2w]) = SOME 2w
Proof
  EVAL_TAC
QED
