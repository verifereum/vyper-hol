Theory functionInlinerIdWitness
Ancestors
  functionInlinerDefs venomInst venomWf
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

(* The helper is removed, but the rewritten entry and the untouched other
   function both have an instruction numbered zero. *)
Theorem inliner_renumbering_duplicates_id:
  ctx_inst_ids_distinct id_witness_ctx /\
  ~ctx_inst_ids_distinct (function_inliner_ctx 0 id_witness_ctx)
Proof
  EVAL_TAC
QED
