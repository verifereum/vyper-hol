Theory bodyPtrPopTraceBoundary
Ancestors bodyPtrPopSavedExecution bodyPtrPopEmptyTaint bodyPtrPopSequenceStep
  vyperValue ptrDiscipline list rich_list venomState

(* These names abbreviate the exact finite prefix computation. Keeping the
   runtime and each ghost component separate avoids substituting whole
   configurations into the remaining instruction sequence. *)
Definition pop_trace_inst_def:
  pop_trace_inst n = EL n pop_saved_code
End
Definition pop_trace_state_def:
  pop_trace_state n =
    case run_inst_seq (TAKE n pop_saved_code) pop_saved_runtime of
      OK u => u with vs_inst_idx := n
    | _ => pop_saved_runtime
End
Definition pop_trace_prov_def:
  pop_trace_prov 0 = FEMPTY /\
  pop_trace_prov (SUC n) =
    case step_inst_base (pop_trace_inst n) (pop_trace_state n) of
      OK u => step_prov [] (pop_trace_prov n) (pop_trace_inst n) u
    | _ => pop_trace_prov n
End
Definition pop_trace_taint_def:
  pop_trace_taint 0 = entry_taint /\
  pop_trace_taint (SUC n) =
    case step_inst_base (pop_trace_inst n) (pop_trace_state n) of
      OK u => step_taint (pop_trace_inst n) (pop_trace_state n) u
        (pop_trace_taint n)
    | _ => pop_trace_taint n
End

Theorem pop_trace_boundary_insts:
  pop_trace_inst 23 = <|inst_id := 23; inst_opcode := ASSERT;
    inst_operands := [Var "%19"]; inst_outputs := []|> /\
  pop_trace_inst 24 = <|inst_id := 24; inst_opcode := ADD;
    inst_operands := [Var "%14"; Lit 1w]; inst_outputs := ["%20"]|>
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC
QED

Theorem pop_trace_boundary_runtime:
  step_inst_base (pop_trace_inst 23) (pop_trace_state 23) =
    OK (pop_trace_state 23) /\
  eval_operand (Var "%19") (pop_trace_state 23) = SOME 1w /\
  (pop_trace_state 23).vs_inst_idx = 23
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem pop_trace_boundary_runtime24:
  pop_trace_state 24 =
    pop_trace_state 23 with vs_inst_idx := 24 /\
  step_inst_base (pop_trace_inst 24) (pop_trace_state 24) =
    OK (update_var "%20" 9w (pop_trace_state 24))
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

(* Project before expanding either the runtime or the earlier ghost. *)
Theorem pop_step_taint_storage_frame:
  inst.inst_opcode <> SSTORE /\ inst.inst_opcode <> CALL ==>
  (step_taint inst s s' tn).t_stor = tn.t_stor
Proof
  simp[step_taint_def, store_taint_def, adopt_reset_def]
QED

Theorem pop_trace_storage_frame:
  (pop_trace_inst n).inst_opcode <> SSTORE /\
  (pop_trace_inst n).inst_opcode <> CALL ==>
  (pop_trace_taint (SUC n)).t_stor = (pop_trace_taint n).t_stor
Proof
  strip_tac >> rewrite_tac[Once pop_trace_taint_def] >>
  Cases_on `step_inst_base (pop_trace_inst n) (pop_trace_state n)` >>
  simp[pop_step_taint_storage_frame]
QED

Theorem pop_trace_storage_opcode_list:
  EVERY (\n. n = 14 \/
    ((pop_trace_inst n).inst_opcode <> SSTORE /\
     (pop_trace_inst n).inst_opcode <> CALL)) (COUNT_LIST 23)
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_storage_exception:
  n < 23 /\ n <> 14 ==>
  (pop_trace_inst n).inst_opcode <> SSTORE /\
  (pop_trace_inst n).inst_opcode <> CALL
Proof
  strip_tac >> mp_tac pop_trace_storage_opcode_list >>
  simp[EVERY_MEM, MEM_COUNT_LIST] >> metis_tac[]
QED

Theorem pop_trace_store14_inst:
  pop_trace_inst 14 = <|inst_id := 14; inst_opcode := SSTORE;
    inst_operands := [Lit 0w; Var "%11"]; inst_outputs := []|>
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss, type_slot_size_def] >> EVAL_TAC
QED

Theorem pop_trace_storage_before_store:
  !n. n <= 14 ==> (pop_trace_taint n).t_stor = {}
Proof
  Induct >- simp[pop_trace_taint_def, entry_taint_def] >> strip_tac >>
  `n < 23 /\ n <> 14 /\ n <= 14` by decide_tac >>
  drule_all pop_trace_storage_exception >> strip_tac >>
  simp[pop_trace_storage_frame]
QED

Theorem pop_trace_store14_storage:
  (pop_trace_taint (SUC 14)).t_stor =
    case step_inst_base (pop_trace_inst 14) (pop_trace_state 14) of
      OK u => key_update {} 0w
        (op_taint (pop_trace_taint 14) (Var "%11"))
    | _ => {}
Proof
  rewrite_tac[Once pop_trace_taint_def] >>
  Cases_on `step_inst_base (pop_trace_inst 14) (pop_trace_state 14)` >>
  simp[step_taint_def, store_taint_def, adopt_reset_def,
    pop_trace_store14_inst, eval_operand_def, pop_trace_storage_before_store]
QED

Theorem pop_trace_storage_after_store:
  !n. 15 <= n /\ n <= 23 ==>
    (pop_trace_taint n).t_stor = (pop_trace_taint 15).t_stor
Proof
  Induct >- simp[] >> strip_tac >>
  Cases_on `n = 14` >- simp[] >>
  `n < 23 /\ n <> 14 /\ 15 <= n /\ n <= 23` by decide_tac >>
  drule_all pop_trace_storage_exception >> strip_tac >>
  simp[pop_trace_storage_frame]
QED

Theorem pop_trace_boundary_storage_residual:
  (pop_trace_taint 23).t_stor =
    case step_inst_base (pop_trace_inst 14) (pop_trace_state 14) of
      OK u => key_update {} 0w
        (op_taint (pop_trace_taint 14) (Var "%11"))
    | _ => {}
Proof
  simp[pop_trace_storage_after_store,
    SIMP_RULE (srw_ss()) [] pop_trace_store14_storage]
QED
