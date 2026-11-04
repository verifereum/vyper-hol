(* Concrete candidate for the reset gate. Parser abbreviations only. *)
Theory lowerDloadProgramProbe
Ancestors
  lowerDloadResetProbe o1PassContract lowerDloadDefs venomInst venomFnScheduleRunner fcgDefs unitShapeDefs

val _ = temp_overload_on ("probe_helper",
  ``mk_raw_function "f" [<|bb_label := "f"; bb_instructions := [
    mk_inst 0 ALLOCA [Lit 32w] ["p"];
    mk_inst 1 MSTORE [Var "p"; Lit 1w] [];
    mk_inst 2 RET [Lit 0w] []] |>]``);
val _ = temp_overload_on ("probe_entry",
  ``mk_raw_function "entry" [<|bb_label := "entry"; bb_instructions := [
    mk_inst 3 INVOKE [Label "f"] [];
    mk_inst 4 DLOAD [Lit 0w] ["d"];
    mk_inst 5 ALLOCA [Lit 32w] ["q"];
    mk_inst 6 MLOAD [Var "q"] ["v"];
    mk_inst 7 SSTORE [Lit 0w; Var "v"] [];
    mk_inst 8 CALL [Lit 0w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["ok"];
    mk_inst 9 SLOAD [Lit 0w] ["w"];
    mk_inst 10 SSTORE [Lit 1w; Var "w"] [];
    mk_inst 11 STOP [] []] |>]``);
val _ = temp_overload_on ("probe_context",
  ``mk_venom_context [probe_entry; probe_helper] (SOME "entry")``);

Theorem probe_entry_targets:
  fn_invoke_targets probe_entry = ["f"]
Proof
  rewrite_tac[fn_invoke_targets_def, fcg_scan_function_def, fn_insts_def,
              mk_raw_function_def, fn_insts_blocks_def] >>
  EVAL_TAC >> rewrite_tac[get_invoke_targets_def] >> EVAL_TAC
QED

Theorem probe_helper_targets:
  fn_invoke_targets probe_helper = []
Proof
  rewrite_tac[fn_invoke_targets_def, fcg_scan_function_def, fn_insts_def,
              mk_raw_function_def, fn_insts_blocks_def] >>
  EVAL_TAC >> rewrite_tac[get_invoke_targets_def] >> EVAL_TAC
QED

Theorem probe_callee_order:
  callee_first ["f"; "entry"] probe_context.ctx_functions
Proof
  simp[callee_first_def, mk_venom_context_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[] >>
  gvs[probe_entry_targets, probe_helper_targets] >> EVAL_TAC
QED

Theorem probe_shape_excluded:
  ~o1_ctx_shape probe_context
Proof
  EVAL_TAC
QED

(* The proposed pseudocode omitted the mandatory CALL success check. *)
Theorem probe_call_check_excluded:
  ~call_checks_ok probe_entry
Proof
  EVAL_TAC
QED
