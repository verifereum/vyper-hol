(* Checked allocation-budget regressions; no execution-memory claims. *)
Theory evalCompilerAllocationBudget
Ancestors vyperCompiler venomInst venomWf words venomExecSemantics
  venomState stackPlanGen fmpLowerDefs
Libs computeLib wordsLib

Definition allocation_budget_test_context_def:
  allocation_budget_test_context sizes =
    mk_venom_context
      [mk_raw_function "__entry"
        [<| bb_label := "__entry";
            bb_instructions :=
              MAP (\(id, size). instruction id ALLOCA [Lit size] ["ptr"]) sizes |>]]
      (SOME "__entry")
End

(* alloca_size is exactly the operand-shape projection, not an opcode or
   output-arity check. Those constraints belong to the instruction semantics
   and wf_inst; the budget filters on ALLOCA separately. *)
Theorem alloca_size_operand_shapes_eval:
  alloca_size (instruction 0 ALLOCA [Lit 32w] ["p"]) = 32 /\
  alloca_size (instruction 0 ALLOCA [Lit 0w] ["p"]) = 0 /\
  alloca_size (instruction 0 ALLOCA [] ["p"]) = 0 /\
  alloca_size (instruction 0 ALLOCA [Var "size"] ["p"]) = 0 /\
  alloca_size (instruction 0 ALLOCA [Label "size"] ["p"]) = 0 /\
  alloca_size (instruction 0 ALLOCA [Lit 32w; Lit 64w] ["p"]) = 0 /\
  alloca_size (instruction 0 DALLOCA [Lit 32w] ["p"]) = 32 /\
  alloca_size (instruction 0 ALLOCA [Lit 32w] []) = 32
Proof
  EVAL_TAC
QED

(* Count both call sites, every block, and the uncalled function's ALLOCA.
   DALLOCA, BUMP, nonallocation literals, and malformed ALLOCA operands contribute
   no static size. An empty function does not change the budget. *)
Theorem unit_alloca_budget_full_context_eval:
  unit_alloca_budget
    (mk_venom_context
      [mk_raw_function "__entry"
        [<| bb_label := "__entry";
            bb_instructions :=
              [instruction 0 ALLOCA [Lit 32w] ["p"];
               instruction 1 INVOKE [Label "callee"] []] |>;
         <| bb_label := "next";
            bb_instructions :=
              [instruction 2 INVOKE [Label "callee"] [];
               instruction 3 DALLOCA [Lit 1024w] ["q"];
               instruction 4 ASSIGN [Lit 999w] ["r"];
               instruction 5 ALLOCA [Var "size"] ["s"]] |>];
       mk_raw_function "callee"
         [<| bb_label := "callee";
             bb_instructions := [instruction 6 ALLOCA [Lit 64w] ["p"]] |>];
       mk_raw_function "uncalled"
         [<| bb_label := "uncalled";
             bb_instructions := [instruction 7 ALLOCA [Lit 16w] ["p"];
               instruction 8 BUMP [Lit 1024w; Lit 1024w] ["old";"new"]] |>];
       mk_raw_function "empty" []]
      (SOME "__entry")) = 336
Proof
  EVAL_TAC
QED

(* A deliberately unaligned BUMP operand distinguishes plain addition from
   the old second rounding. DALLOCA supplies alignment before this boundary. *)
Theorem bump_plain_add_eval:
  step_inst_base (mk_inst 0 BUMP [Lit 64w; Lit 1w] ["old";"new"]) s =
    OK (update_var "new" 65w (update_var "old" 64w s)) /\
  bump_emit_ops = [SODup 2; SOEmit "ADD"]
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
       bump_emit_ops_def]
QED

Definition allocation_lowering_test_supply_def:
  allocation_lowering_test_supply =
    <| irs_next_inst := 1; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |>
End

(* Check the production emission, including restores before DALLOCA and JNZ,
   generated-ID order, and rejection of an endpoint by leaving it unconsumed.
   Source instruction IDs deliberately differ from original list indices. *)
Theorem allocation_lowering_original_points_eval:
  OPTION_MAP (\(code,leftover,supply).
    (MAP (\i. i.inst_opcode) code, MAP (\i. i.inst_id) code,
     MAP (\i. i.inst_operands) code, leftover))
    (fmp_lower_indexed FEMPTY ctx "runner" "entry" 0
      allocation_lowering_test_supply
      [(("entry",0),"mark"); (("entry",1),"p"); (("entry",2),"endpoint")]
      [mk_inst 70 DALLOCA [Lit 1w] ["p"];
       mk_inst 400 JNZ [Var "flag";Label "yes";Label "no"] []]) =
  SOME ([ASSIGN;ADD;NOT;AND;BUMP;ASSIGN;JNZ], [1;2;3;4;5;6;400],
    [[Var "mark"]; [Lit 1w;Lit 31w]; [Lit 31w];
     [Var "formal_var_0";Var "formal_var_1"];
     [Var "runner";Var "formal_var_2"]; [Var "p"];
     [Var "flag";Label "yes";Label "no"]], [(("entry",2),"endpoint")])
Proof
  EVAL_TAC
QED

Theorem allocation_budget_empty_eval:
  unit_alloca_budget (mk_venom_context [] NONE) = 0 /\
  lowering_context_ok (allocation_budget_test_context [])
Proof
  EVAL_TAC
QED

Theorem allocation_budget_strict_boundary_eval:
  lowering_context_ok
    (allocation_budget_test_context [(0, n2w (2 ** 256 - 1))]) /\
  unit_alloca_budget
    (allocation_budget_test_context [(0, n2w (2 ** 255));
                                     (1, n2w (2 ** 255))]) = 2 ** 256 /\
  ~lowering_context_ok
    (allocation_budget_test_context [(0, n2w (2 ** 255));
                                     (1, n2w (2 ** 255))]) /\
  unit_alloca_budget
    (allocation_budget_test_context [(0, n2w (2 ** 256 - 1));
                                     (1, n2w (2 ** 256 - 1))]) > 2 ** 256 /\
  ~lowering_context_ok
    (allocation_budget_test_context [(0, n2w (2 ** 256 - 1));
                                     (1, n2w (2 ** 256 - 1))])
Proof
  EVAL_TAC
QED

(* The old integrity conjuncts hold; only the INVOKE multiplier makes the
   strengthened compiler guard reject this unit. *)
Definition allocation_budget_invoke_context_def:
  allocation_budget_invoke_context =
    mk_venom_context
      [mk_raw_function "__entry"
        [<| bb_label := "__entry";
            bb_instructions :=
              [instruction 0 INVOKE [Label "callee"] []] |>];
       mk_raw_function "callee"
         [<| bb_label := "callee";
             bb_instructions :=
               [instruction 1 ALLOCA [Lit (n2w (2 ** 255))] ["p"]] |>]]
      (SOME "__entry")
End

Theorem allocation_budget_invoke_multiplier_rejects_eval:
  ALL_DISTINCT (ctx_fn_names allocation_budget_invoke_context) /\
  wf_invoke_targets_check allocation_budget_invoke_context /\
  ctx_inst_ids_distinct allocation_budget_invoke_context /\
  forced_alloc_inputs_check allocation_budget_invoke_context /\
  unit_alloca_budget allocation_budget_invoke_context = 2 ** 256 /\
  ~lowering_context_ok allocation_budget_invoke_context
Proof
  EVAL_TAC
QED
