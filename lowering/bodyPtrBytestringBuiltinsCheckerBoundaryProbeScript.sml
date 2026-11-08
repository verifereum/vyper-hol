Theory bodyPtrBytestringBuiltinsCheckerBoundaryProbe
Ancestors bodyPtrBytestringBuiltinsTerminalInstallProbe
          bodyPtrBytestringBuiltinsTerminalPairProbe
          bodyPtrBytestringBuiltinsImageFrontier vyperCompiler venomInst

(* Finite checker probes: neither fixture asserts an admissible body frame. *)
Definition checker_probe_fn_def:
  checker_probe_fn = mk_raw_function "entry"
    [<|bb_label := "entry"; bb_instructions :=
      terminal_probe_final.cs_current_insts ++ [mk_inst 4 STOP [] []]|>]
End

Theorem checker_probe_window_accepted:
  fn_ptr_ok_check (K []) checker_probe_fn /\ wf_function checker_probe_fn /\
  image_bad terminal_probe_final.cs_current_insts
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  irule terminal_probe_collision
QED

Definition checker_probe_context_def:
  checker_probe_context = FST (THE terminal_install_extracted)
End
Definition checker_probe_entry_def:
  checker_probe_entry = HD checker_probe_context.ctx_functions
End

Theorem checker_probe_closures:
  (pv_closure checker_probe_entry (opcode_root_list ALLOCA checker_probe_entry),
   pv_closure checker_probe_entry [],
   opcode_root_list ALLOCA checker_probe_entry) =
    (SOME ["%8"; "%10"; "%9"], SOME [], ["%8"; "%10"])
Proof
  EVAL_TAC
QED

Theorem checker_probe_other_roots:
  opcode_root_list DALLOCA checker_probe_entry = [] /\
  param_root_list (ctx_ptr_param_list checker_probe_context checker_probe_entry.fn_name)
    checker_probe_entry = []
Proof
  EVAL_TAC
QED

Definition checker_probe_invoke_def:
  checker_probe_invoke = HD (FILTER (\i. i.inst_opcode = INVOKE)
    (fn_insts checker_probe_entry))
End

Theorem checker_probe_invoke_shape:
  (checker_probe_invoke.inst_id, checker_probe_invoke.inst_operands,
   checker_probe_invoke.inst_outputs) =
    (17,[Label "internal 0 sink()_runtime"; Var "%9"; Var "%10"],[])
Proof
  EVAL_TAC
QED

Theorem checker_probe_invoke_parameters:
  ctx_ptr_param_list checker_probe_context "internal 0 sink()_runtime" = []
Proof
  EVAL_TAC
QED

Theorem checker_probe_invoke_checks:
  (inst_ptr_ok_check (ctx_ptr_param_list checker_probe_context)
     ["%8"; "%10"; "%9"] checker_probe_invoke,
   affine_check ["%8"; "%10"; "%9"] checker_probe_invoke,
   phi_check ["%8"; "%10"; "%9"] checker_probe_invoke,
   write_excl_check ["%8"; "%10"; "%9"] [] checker_probe_invoke) = (F,T,T,T)
Proof
  EVAL_TAC
QED

Theorem checker_probe_accepted_bad_block:
  fn_ptr_ok_check (K []) checker_probe_fn /\
  image_bad (HD checker_probe_fn.fn_blocks).bb_instructions
Proof
  conj_tac >- EVAL_TAC >>
  simp[checker_probe_fn_def, mk_raw_function_def, terminal_probe_final_def,
    image_bad_def] >>
  qexistsl [`0`, `1`, `2`, `3`, `32w`, `"%0"`, `"%1"`, `"%2"`, `[]`,
    `[mk_inst 4 STOP [] []]`] >> simp[]
QED
