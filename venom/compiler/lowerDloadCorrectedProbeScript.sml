(* Shape-only checkpoint for a separately named corrected reset candidate. *)
Theory lowerDloadCorrectedProbe
Ancestors
  lowerDloadProgramProbe o1PassContract lowerDloadDefs venomInst
  venomFnScheduleRunner fcgDefs unitShapeDefs

val _ = temp_overload_on ("corrected_helper",
  ``mk_raw_function "f" [<|bb_label := "f"; bb_instructions := [
    mk_inst 0 ALLOCA [Lit 32w] ["p"];
    mk_inst 1 MSTORE [Var "p"; Lit 1w] [];
    mk_inst 2 RET [Lit 0w] []] |>]``);
val _ = temp_overload_on ("corrected_entry",
  ``mk_raw_function "entry" [<|bb_label := "entry"; bb_instructions := [
    mk_inst 3 INVOKE [Label "f"] [];
    mk_inst 4 DLOAD [Lit 0w] ["d"];
    mk_inst 5 ALLOCA [Lit 32w] ["q"];
    mk_inst 6 MLOAD [Var "q"] ["v"];
    mk_inst 7 SSTORE [Lit 0w; Var "v"] [];
    mk_inst 8 CALL [Lit 0w; Lit 256w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w] ["ok"];
    mk_inst 9 ASSERT [Var "ok"] [];
    mk_inst 10 SLOAD [Lit 0w] ["w"];
    mk_inst 11 SSTORE [Lit 1w; Var "w"] [];
    mk_inst 12 STOP [] []] |>]``);
val _ = temp_overload_on ("corrected_context",
  ``mk_venom_context [corrected_entry; corrected_helper] (SOME "entry")``);

Theorem corrected_no_opaque_seeds:
  !fn origin. MEM fn [corrected_entry; corrected_helper] /\
    MEM origin [GAS; RETPC_PARAM] ==>
    !x. ~copy_phi_var origin fn x
Proof
  rpt gen_tac >> strip_tac >> irule copy_phi_var_no_seed >>
  gvs[] >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem corrected_opaque:
  !fn. MEM fn [corrected_entry; corrected_helper] ==> opaque_use_ok fn
Proof
  rpt strip_tac >> simp[opaque_use_ok_def, gas_var_def, retpc_var_def] >>
  metis_tac[corrected_no_opaque_seeds, listTheory.MEM]
QED

Theorem corrected_invoke_syntax:
  !fn. MEM fn [corrected_entry; corrected_helper] ==>
    fn_invoke_ok ["entry"; "f"] fn /\ fn_label_refs_ok fn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[fn_invoke_ok_def, fn_label_refs_ok_def, fn_insts_def,
       mk_raw_function_def, fn_insts_blocks_def, mk_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem corrected_shape:
  o1_ctx_shape corrected_context
Proof
  `opaque_use_ok corrected_entry /\ opaque_use_ok corrected_helper` by
    metis_tac[corrected_opaque, listTheory.MEM] >>
  `fn_invoke_ok ["entry"; "f"] corrected_entry /\
   fn_invoke_ok ["entry"; "f"] corrected_helper /\
   fn_label_refs_ok corrected_entry /\ fn_label_refs_ok corrected_helper` by
    metis_tac[corrected_invoke_syntax, listTheory.MEM] >>
  `ctx_fn_names corrected_context = ["entry"; "f"]` by EVAL_TAC >>
  gvs[mk_venom_context_def] >>
  simp[o1_ctx_shape_def, o1_fn_shape_def, fn_shape_ok_def] >>
  rpt conj_tac >> EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem corrected_callee_order:
  callee_first ["f"; "entry"] corrected_context.ctx_functions
Proof
  simp[callee_first_def, mk_venom_context_def] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- (`fn_invoke_targets corrected_entry = ["f"]` by
        (rewrite_tac[fn_invoke_targets_def, fcg_scan_function_def, fn_insts_def,
                     mk_raw_function_def, fn_insts_blocks_def] >>
         EVAL_TAC >> rewrite_tac[get_invoke_targets_def] >> EVAL_TAC) >>
      gvs[] >> EVAL_TAC) >>
  gvs[probe_helper_targets]
QED
