(* Empty argument vectors are valid internal calls, not empty functions.
 * TOP-LEVEL: invoke_zero_args_returns_seven, invoke_empty_function_rejected.
 * The regression uses no PARAMs and no synthetic INVOKE argument; RETPC_PARAM
 * reads the default token and RET returns one value under the existing ABI. *)
Theory invokeEmptyArgs
Ancestors
  venomExecSemantics venomState venomInst finite_map list

Definition zero_args_callee_def:
  zero_args_callee = mk_raw_function "bar"
    [<| bb_label := "bar";
        bb_instructions :=
          [instruction 0 RETPC_PARAM [Lit 0w] ["pc"];
           instruction 1 RET [Lit 7w; Var "pc"] []] |>]
End

Definition zero_args_context_def:
  zero_args_context = mk_venom_context [zero_args_callee] (SOME "bar")
End

(* The entire callee record equation checks every inherited field, including
 * memory, accounts, call contexts and the global allocation cursor. *)
Theorem setup_zero_args_preserves_frame:
  !s.
    setup_callee zero_args_callee [] s =
    SOME (s with <| vs_vars := FEMPTY; vs_params := [];
      vs_current_bb := "bar"; vs_inst_idx := 0; vs_prev_bb := NONE;
      vs_halted := F; vs_allocas := FEMPTY;
      vs_fmp := s.vs_fmp; vs_call_entry_fmp := s.vs_fmp;
      vs_return_pc_token := 0w |>)
Proof
  simp[setup_callee_def, zero_args_callee_def, mk_raw_function_def]
QED

Theorem setup_empty_function_rejected:
  !args s. setup_callee (mk_raw_function "bar" []) args s = NONE
Proof
  simp[setup_callee_def, mk_raw_function_def]
QED

Theorem invoke_zero_args_returns_seven:
  !s.
    step_inst 1 zero_args_context
      (instruction 2 INVOKE [Label "bar"] ["answer"]) s =
    OK (update_var "answer" 7w s)
Proof
  simp[Once step_inst_def, decode_invoke_def, zero_args_context_def,
       mk_venom_context_def, lookup_function_def, zero_args_callee_def,
       mk_raw_function_def, FIND_thm, eval_operands_def, setup_callee_def] >>
  simp[Once run_blocks_def, lookup_block_def, FIND_thm, eval_phis_def,
       phi_prefix_length_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
       step_inst_base_def, is_terminator_def, eval_operands_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, bind_outputs_def,
       adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem invoke_empty_function_rejected:
  !fuel s.
    step_inst fuel (mk_venom_context [mk_raw_function "bar" []] NONE)
      (instruction 2 INVOKE [Label "bar"] ["answer"]) s =
    Error "invoke: empty function"
Proof
  simp[Once step_inst_def, decode_invoke_def, mk_venom_context_def,
       lookup_function_def, mk_raw_function_def, FIND_thm, eval_operands_def,
       setup_callee_def]
QED
