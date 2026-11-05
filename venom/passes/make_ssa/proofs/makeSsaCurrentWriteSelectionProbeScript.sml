Theory makeSsaCurrentWriteSelectionProbe
Ancestors makeSsaCurrentChronologicalTransition makeSsaCurrentDefs
  venomWf venomExecSemantics venomState irSupply alist list

(* BUMP is the sole well-formed non-call multi-output ordinary opcode. *)
Theorem current_bump_repeated_outputs_wf_probe:
  inst_wf <| inst_id := 0; inst_opcode := BUMP;
    inst_operands := [Lit 3w; Lit 4w]; inst_outputs := ["x";"x"] |>
Proof
  EVAL_TAC
QED

Theorem current_bump_repeated_write_probe:
  step_inst_base <| inst_id := 0; inst_opcode := BUMP;
    inst_operands := [Lit 3w; Lit 4w]; inst_outputs := ["x";"x"] |> st =
  OK (update_var "x" (3w + 4w) (update_var "x" 3w st))
Proof
  simp[step_inst_base_def, eval_operand_def, wordsTheory.WORD_ADD_0] >> EVAL_TAC
QED

Theorem current_repeated_output_selection_probe:
  rename_current_outputs s ([],[]) ["x";"x"] = (rt,s',names) ==>
  LENGTH names = 2 /\ EL 0 names = "x" /\
  latest_current_name rt "x" = EL 1 names
Proof
  Cases_on `fresh_ir_var s` >>
  simp[rename_current_outputs_def, push_current_name_def, latest_current_name_def] >>
  rpt strip_tac >> gvs[latest_current_name_def]
QED

Definition current_selection_probe_supply_def:
  current_selection_probe_supply = <| irs_next_inst := 0; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := []; irs_used_vars := ["x"];
    irs_used_labels := [] |>
End

Theorem current_repeated_output_distinct_selection_probe:
  EL 0 (SND (SND (rename_current_outputs current_selection_probe_supply ([],[]) ["x";"x"]))) = "x" /\
  EL 1 (SND (SND (rename_current_outputs current_selection_probe_supply ([],[]) ["x";"x"]))) = "formal_var_0" /\
  latest_current_name
    (FST (rename_current_outputs current_selection_probe_supply ([],[]) ["x";"x"])) "x" = "formal_var_0" /\
  "x" <> "formal_var_0"
Proof
  EVAL_TAC
QED

(* Write-selection audit (step_inst_base = OK only, inst_wf assumed).
   - Zero-output: writes/copies, JMP/JNZ/DJMP, SETFMP, LOG, assertions,
     NOP. Their successful executions do not update the variable store.
     RET/RETFMP/DRET, STOP/RETURN/REVERT, SINK, INVALID, SELFDESTRUCT
     have no OK result (hence do not enter this boundary).
   - One-output: pure1/2/3, read0/1, ASSIGN, PARAM/FMP_PARAM/RETPC_PARAM,
     ALLOCA/DALLOCA, GETFMP/INITIAL_FMP, SHA3/OFFSET, external
     CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2. Successful paths write
     that sole output. External call failure values are still writes.
   - Two ordered outputs: BUMP only. Repeated destinations are permitted;
     ptr is written first, next second. The probes above check this case.
   - INVOKE: step_inst_base falls through to Error; the separate exec_inst
     call boundary must handle arbitrary return arity and is NOT proved here.
   No genuine partial-declared-output case was found for well-formed OK
   ordinary steps. In particular malformed NOP output examples are irrelevant.
   A universal full-write-witness theorem is NOT supplied by this audit.

   Existing static interfaces:
   current_push_latest: push_current_name s rs v = (rs',s',n) implies
     latest_current_name rs' w = if w=v then n else latest_current_name rs w.
   current_outputs_trace_exit_env: E' is the ordered FOLDL of token updates.
   current_outputs_trace_names / current_local_original_output_name identify
     each target output name from its original occurrence token.
   current_outputs_trace_owned_names puts every target output in history H'.
   current_owner_name_separate excludes names belonging to distinct owners
     under current_history_valid V H' and owner membership in V.
   current_outputs_trace_preserves preserves allocation/environment validity.

   Missing composing static interface (not an additional alignment premise):
   From current_outputs_trace anns s rs H E names s' rt H' E',
   current_allocation_consistent V H s rs, current_env_realizes H E rs V,
   and current_annotations_ok V H anns,
   derive for every v: if j is the last index in anns whose SND is v,
   then latest_current_name rt v = EL j names and no later target output
   hits that name; if no such index exists then latest_current_name rt v =
   latest_current_name rs v and no target output hits that selected name
   (with MEM v V for cross-owner exclusion). The intended runtime consumer
   uses the full ordered actual-write witness, so chronological event position
   and output position agree; arbitrary indexed_writes witnesses alone are
   weaker and do not imply full writes. Incoming equality remains needed for
   demanded v not in MAP SND anns, never for a well-formed declared output
   which was supposedly ignored.
*)
