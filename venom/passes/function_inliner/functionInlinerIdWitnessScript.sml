Theory functionInlinerIdWitness
Ancestors
  functionInlinerContract functionInlinerDefs fcgDefs vyperCompiler
  venomInst venomWf
Libs
  finite_mapLib wordsLib

Definition id_witness_ctx_def:
  id_witness_ctx = mk_venom_context
    [mk_raw_function "entry"
       [<| bb_label := "entry"; bb_instructions :=
             [<| inst_id := 1; inst_opcode := INVOKE;
                 inst_operands := [Label "helper"]; inst_outputs := [] |>;
              <| inst_id := 2; inst_opcode := STOP;
                 inst_operands := []; inst_outputs := [] |>] |>];
     mk_raw_function "helper"
       [<| bb_label := "helper"; bb_instructions :=
             [<| inst_id := 3; inst_opcode := RETPC_PARAM;
                 inst_operands := [Lit 0w]; inst_outputs := ["pc"] |>;
              <| inst_id := 4; inst_opcode := RET;
                 inst_operands := [Var "pc"]; inst_outputs := [] |>] |>];
     mk_raw_function "other"
       [<| bb_label := "other"; bb_instructions :=
             [<| inst_id := 0; inst_opcode := RETPC_PARAM;
                 inst_operands := [Lit 0w]; inst_outputs := ["other_pc"] |>;
              <| inst_id := 5; inst_opcode := RET;
                 inst_operands := [Var "other_pc"]; inst_outputs := [] |>] |>]]
    (SOME "entry")
End

(* The entry is rewritten, while the untouched function keeps instruction
   zero. This context collided when rewriting renumbered the caller from 0. *)
Theorem inliner_preserves_witness_ids:
  ctx_inst_ids_distinct id_witness_ctx /\
  ctx_inst_ids_distinct (function_inliner_ctx 0 id_witness_ctx) /\
  MAP (\fn. fn.fn_name) (function_inliner_ctx 0 id_witness_ctx).ctx_functions =
    ["entry"; "other"]
Proof
  EVAL_TAC
QED

Definition dead_caller_witness_ctx_def:
  dead_caller_witness_ctx =
    let other = mk_raw_function "other"
          [<| bb_label := "other"; bb_instructions :=
                [mk_inst 0 RETPC_PARAM [Lit 0w] ["other_pc"];
                 mk_inst 6 INVOKE [Label "helper"] [];
                 mk_inst 5 RET [Var "other_pc"] []] |>] in
    id_witness_ctx with ctx_functions :=
      TAKE 2 id_witness_ctx.ctx_functions ++ [other]
End

(* The entry's call is rewritten, but the dead caller is left alone.
   Its call targets the function removed in the same inlining round. *)
Theorem inliner_retains_dead_caller_with_removed_target:
  C = dead_caller_witness_ctx /\
  walk = build_call_walk (fcg_analyze C) "entry" /\
  ist = <| is_inline_count := 0; is_label_counter := 0;
                is_next_inst_id := 7 |> ==>
  lowering_context_ok C /\
  (case function_inliner_round C walk 0 ist of
     NONE => F
   | SOME (out, _, _) =>
       lookup_function "helper" out.ctx_functions = NONE /\
       (case lookup_function "other" out.ctx_functions of
          NONE => F
        | SOME caller => EXISTS (\inst. inst.inst_opcode = INVOKE /\
                                   inst.inst_operands = [Label "helper"])
                                (fn_insts caller)) /\
       ~wf_invoke_targets out) /\
  ~wf_invoke_targets (function_inliner_ctx 0 C)
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac std_ss [GSYM wf_invoke_targets_check_eq] >> EVAL_TAC
QED

Theorem inliner_dead_caller_projection:
  out = function_inliner_ctx 0 dead_caller_witness_ctx ==>
  MAP (\fn. fn.fn_name) (reachable_ctx out).ctx_functions = ["entry"] /\
  wf_invoke_targets (reachable_ctx out)
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp_tac std_ss [GSYM wf_invoke_targets_check_eq] >> EVAL_TAC
QED
