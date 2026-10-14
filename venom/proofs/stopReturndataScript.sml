(* STOP discards a prior callee's return data, even for a void return.
 * TOP-LEVEL: step_stop_clears_returndata, stop_after_callee_returndata.
 * The non-empty regression starts from the state left by a callee;
 * it does not assume that return data was empty before STOP. *)
Theory stopReturndata
Ancestors
  venomExecSemantics venomState venomInst

Theorem step_stop_clears_returndata:
  !fuel ctx inst s.
    inst.inst_opcode = STOP ==>
    step_inst fuel ctx inst s = Halt (halt_state (s with vs_returndata := []))
Proof
  rpt strip_tac >> simp[step_inst_non_invoke, step_inst_base_def]
QED

(* Concrete stale bytes plus an otherwise arbitrary caller state. *)
Theorem stop_after_callee_returndata:
  !fuel ctx s.
    exec_block fuel ctx
      <| bb_label := "void_return";
         bb_instructions := [instruction 0 STOP [] []] |>
      (s with <| vs_inst_idx := 0; vs_returndata := [42w; 7w] |>) =
    Halt (halt_state (s with <| vs_inst_idx := 0; vs_returndata := [] |>))
Proof
  rpt gen_tac >> simp[Once exec_block_def, get_instruction_def] >>
  simp[step_stop_clears_returndata, halt_state_def]
QED

(* Exact witness against the old unconditional STOP-state equation. *)
Theorem stop_stale_returndata_counterexample:
  !fuel ctx s.
    step_inst fuel ctx (instruction 0 STOP [] [])
      (s with vs_returndata := [42w; 7w]) <>
    Halt (halt_state (s with vs_returndata := [42w; 7w]))
Proof
  rpt gen_tac >> simp[step_stop_clears_returndata] >> strip_tac >>
  pop_assum (mp_tac o AP_TERM ``λ(st:venom_state). st.vs_returndata``) >>
  simp[halt_state_def]
QED
