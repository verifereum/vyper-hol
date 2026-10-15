(* Checked allocation-budget regressions; no execution-memory claims. *)
Theory evalCompilerAllocationBudget
Ancestors vyperCompiler venomInst venomWf words
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
   DALLOCA, nonallocation literals, and malformed ALLOCA operands contribute
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
             bb_instructions := [instruction 7 ALLOCA [Lit 16w] ["p"]] |>];
       mk_raw_function "empty" []]
      (SOME "__entry")) = 336
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
