Theory makeSsaCurrentActualRetention
Ancestors
  makeSsaCurrentOutputNames makeSsaCurrentExitTokens makeSsaCurrentRetention
  makeSsaCurrentFinalSlots venomWf venomInst list

(* Extra predecessor labels are permitted by the frozen input contract.
   This probes the retention proof's proposed witness-to-event step, not
   the semantic correctness of the pass. *)
Definition current_extra_slot_phi_def:
  current_extra_slot_phi = mk_inst 2 PHI
    [Label "E"; Var "a"; Label "Ghost"; Var "b"; Label "Phantom"; Var "c"] ["v"]
End

Definition current_extra_slot_fn_def:
  current_extra_slot_fn = mk_raw_function "extra_slots"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 ASSIGN [Lit 1w] ["a"]; mk_inst 1 JMP [Label "D"] []] |>;
     <| bb_label := "D"; bb_instructions :=
        [current_extra_slot_phi; mk_inst 3 STOP [] []] |>]
End

Theorem current_extra_slot_witness_probe:
  inst_wf current_extra_slot_phi /\
  phi_pairs current_extra_slot_phi.inst_operands =
    [("E","a"); ("Ghost","b"); ("Phantom","c")] /\
  fn_cfg_edge current_extra_slot_fn "E" "D" /\
  ~fn_cfg_edge current_extra_slot_fn "Ghost" "D" /\
  ~fn_cfg_edge current_extra_slot_fn "Phantom" "D"
Proof
  EVAL_TAC >>
  pure_rewrite_tac[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >>
  simp[] >> qexists_tac `EL 0 current_extra_slot_fn.fn_blocks` >> EVAL_TAC
QED

Theorem current_extra_slot_input_probe:
  fn_inst_wf current_extra_slot_fn /\
  fn_phis_non_degenerate current_extra_slot_fn
Proof
  conj_tac >- EVAL_TAC >>
  simp[fn_phis_non_degenerate_def, fn_insts_def, fn_insts_blocks_def,
    current_extra_slot_fn_def, current_extra_slot_phi_def, mk_raw_function_def,
    mk_inst_def] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`"E"`, `"a"`, `"Ghost"`, `"b"`] >> EVAL_TAC
QED
