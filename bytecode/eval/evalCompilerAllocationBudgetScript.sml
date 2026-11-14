(* Checked allocation-budget regressions; no execution-memory claims. *)
Theory evalCompilerAllocationBudget
Ancestors vyperCompiler venomInst venomWf words venomExecSemantics
  venomState stackPlanGen fmpLowerDefs allocLimits
Libs computeLib wordsLib

(* Every block ends in a terminator, so the test units are well-formed
   functions, which lowering_context_ok's ptr_ok_check asks for. *)
Definition allocation_budget_test_context_def:
  allocation_budget_test_context sizes =
    mk_venom_context
      [mk_raw_function "__entry"
        [<| bb_label := "__entry";
            bb_instructions :=
              MAP (\(id, size). instruction id ALLOCA [Lit size] ["ptr"]) sizes ++
              [instruction 1000 STOP [] []] |>]]
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
    [[Var "mark"]; [Lit 31w;Lit 1w]; [Lit 31w];
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
    (allocation_budget_test_context [(0, n2w (2 ** 254 - 1))]) /\
  ~lowering_context_ok
    (allocation_budget_test_context [(0, n2w (2 ** 254))]) /\
  ~lowering_context_ok
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
              [instruction 0 INVOKE [Label "callee"] [];
               instruction 2 STOP [] []] |>];
       mk_raw_function "callee"
         [<| bb_label := "callee";
             bb_instructions :=
               [instruction 1 ALLOCA [Lit (n2w (2 ** 253))] ["p"];
                instruction 3 RET [] []] |>]]
      (SOME "__entry")
End

Theorem allocation_budget_invoke_multiplier_rejects_eval:
  ALL_DISTINCT (ctx_fn_names allocation_budget_invoke_context) /\
  wf_invoke_targets_check allocation_budget_invoke_context /\
  ctx_inst_ids_distinct allocation_budget_invoke_context /\
  forced_alloc_inputs_check allocation_budget_invoke_context /\
  unit_alloca_budget allocation_budget_invoke_context = 2 ** 254 /\
  ~lowering_context_ok allocation_budget_invoke_context
Proof
  EVAL_TAC
QED

Definition allocation_budget_dload_context_def:
  allocation_budget_dload_context size =
    mk_venom_context
      [mk_raw_function "__entry"
        [<| bb_label := "__entry";
            bb_instructions :=
              [instruction 0 ALLOCA [Lit (n2w size)] ["p"];
               instruction 1 DLOAD [Lit 0w] ["word"];
               instruction 2 STOP [] []] |>]]
      (SOME "__entry")
End

Theorem allocation_budget_dload_boundary_eval:
  lowering_context_ok (allocation_budget_dload_context (2 ** 254 - 33)) /\
  unit_alloca_budget (allocation_budget_dload_context (2 ** 254 - 32)) =
    2 ** 254 - 32 /\
  ~lowering_context_ok (allocation_budget_dload_context (2 ** 254 - 32))
Proof
  EVAL_TAC
QED

Definition allocation_plan_test_context_def:
  allocation_plan_test_context eom =
    mk_venom_context
      [(mk_raw_function "__entry"
        [<| bb_label := "__entry";
            bb_instructions := [instruction 0 STOP [] []] |>])
        with fn_eom := SOME eom]
      (SOME "__entry")
End

(* The static end and spill end both pass through ceil32 before the gate. *)
Theorem allocation_plan_static_boundary_eval:
  IS_SOME (generate_context_plan_with
    (\fn base labels. SOME ([], init_plan_state base))
    (allocation_plan_test_context (2 ** 254 - 32))) /\
  generate_context_plan_with
    (\fn base labels. SOME ([], init_plan_state base))
    (allocation_plan_test_context (2 ** 254 - 31)) = NONE /\
  generate_context_plan_with
    (\fn base labels. SOME ([], init_plan_state base))
    (allocation_plan_test_context (2 ** 254)) = NONE
Proof
  EVAL_TAC
QED

Theorem allocation_plan_spill_boundary_eval:
  IS_SOME (generate_context_plan_with
    (\fn base labels. SOME ([], (init_plan_state base) with
      ps_alloc updated_by (\al. al with sa_next_offset := 2 ** 254 - 32)))
    (allocation_plan_test_context 0)) /\
  generate_context_plan_with
    (\fn base labels. SOME ([], (init_plan_state base) with
      ps_alloc updated_by (\al. al with sa_next_offset := 2 ** 254 - 31)))
    (allocation_plan_test_context 0) = NONE
Proof
  EVAL_TAC
QED

(* CREATE checker fixtures; no producer change. *)
Theorem create_raw_alloc_boundary_eval:
  let w = Name (BaseT (UintT 256)) "word";
      a = \n. Name (ArrayT (BaseT (UintT 256)) (Fixed n)) "args" in
    ext_call_alloc_ok cenv (CreateTarget RawCreate F T [])
      [w;w;a (2 ** 59 - 1537)] /\
    ~ext_call_alloc_ok cenv (CreateTarget RawCreate F T [])
      [w;w;a (2 ** 59 - 1536)] /\
    ext_call_alloc_ok cenv (CreateTarget RawCreate T F [7;2])
      [w;w;a (2 ** 59 - 1537);w] /\
    ~ext_call_alloc_ok cenv (CreateTarget RawCreate T F [7;2])
      [w;w;a (2 ** 59 - 1536);w]
Proof
  EVAL_TAC
QED

Theorem create_blueprint_alloc_boundary_eval:
  let w = Name (BaseT (UintT 256)) "word";
      a = \n. Name (ArrayT (BaseT (UintT 256)) (Fixed n)) "args" in
    ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T [])
      [w;w;w;a (2 ** 59 - 1)] /\
    ~ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T [])
      [w;w;w;a (2 ** 59)] /\
    ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) T F [2;3])
      [w;w;w;w;a (2 ** 59 - 1)] /\
    ~ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) T F [2;3])
      [w;w;w;w;a (2 ** 59)] /\
    ~ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T [])
      [w;w;w;a (2 ** 58);a (2 ** 58)]
Proof
  EVAL_TAC
QED

(* Empty, raw, fixed-buffer, and malformed cases allocate no new variable
   static constructor buffer. Their operands remain checked recursively. *)
Theorem create_alloc_nonallocating_paths_eval:
  let w = Name (BaseT (UintT 256)) "word";
      huge = Name (ArrayT (BaseT (UintT 256)) (Fixed (2 ** 59))) "args" in
    ext_call_alloc_ok cenv (CreateTarget RawCreate F T []) [w;w] /\
    ext_call_alloc_ok cenv (CreateTarget RawCreate T T []) [w;w;w] /\
    ext_call_alloc_ok cenv (CreateTarget RawCreate T T []) [w;w] /\
    ext_call_alloc_ok cenv (CreateTarget RawCreate F T []) [w] /\
    ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T []) [w;w;w] /\
    ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) T T []) [w;w;w] /\
    ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint T) F T [])
      [w;w;w;huge] /\
    ext_call_alloc_ok cenv (CreateTarget CreateCopyOf F T []) [w;w;huge] /\
    ext_call_alloc_ok cenv (CreateTarget CreateMinimalProxy F T []) [w;w;huge]
Proof
  EVAL_TAC
QED

(* Struct metadata can describe a larger staging footprint than its ABI
   fields. The checker must use the environment's actual physical size. *)
Theorem create_alloc_struct_environment_eval:
  let w = Name (BaseT (UintT 256)) "word";
      arg = Name (StructT (NONE,"S")) "args";
      c = cenv with ce_struct_fields :=
        FEMPTY |+ ("S", [("field", BaseT (UintT 256), 2 ** 64)]) in
    abi_size_bound c.ce_struct_fields (TupleT [expr_type arg]) = 32 /\
    type_memory_bytes c (TupleT [expr_type arg]) = 2 ** 64 /\
    ~ext_call_alloc_ok c (CreateTarget RawCreate F T []) [w;w;arg] /\
    ~ext_call_alloc_ok c (CreateTarget (CreateFromBlueprint F) F T [])
      [w;w;w;arg]
Proof
  EVAL_TAC
QED
