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
Definition allocation_test_word_def:
  allocation_test_word = Name (BaseT (UintT 256)) "word"
End

Definition allocation_test_array_def:
  allocation_test_array n =
    Name (ArrayT (BaseT (UintT 256)) (Fixed n)) "args"
End

Overload allocation_test_bytecode[local] =
  ``\n. Name (BaseT (BytesT (Dynamic n))) "bytecode"``

(* The literal occupies five bytes even under a Bytes[64] annotation.
   The compiler emits a 64-byte literal buffer, a 64-byte snapshot, and
   a 37-byte buffer for the five initcode bytes and one ABI word.
   The shared encoder then allocates its 32-byte cursor. *)
Theorem create_raw_physical_allocations_eval:
  MAP alloca_size (FILTER (\i. i.inst_opcode = ALLOCA)
    (SND (compile_raw_create compile_expr cenv
      (Literal (BaseT (BytesT (Dynamic 64))) (BytesL [96w;0w;96w;0w;243w]))
      (Literal (BaseT (UintT 256)) (IntL 0))
      [Literal (BaseT (UintT 256)) (IntL 7)] NONE F
      (initial_compile_state "entry"))).cs_current_insts) = [64;64;37;32]
Proof
  EVAL_TAC
QED

Theorem create_raw_alloc_boundary_eval:
  ext_call_alloc_ok cenv (CreateTarget RawCreate F T [])
    [allocation_test_bytecode 64;allocation_test_word;allocation_test_array (2 ** 59 - 3)] /\
  ~ext_call_alloc_ok cenv (CreateTarget RawCreate F T [])
    [allocation_test_bytecode 64;allocation_test_word;allocation_test_array (2 ** 59 - 2)] /\
  ext_call_alloc_ok cenv (CreateTarget RawCreate F T [])
    [allocation_test_bytecode 32;allocation_test_word;allocation_test_array (2 ** 59 - 2)] /\
  ext_call_alloc_ok cenv (CreateTarget RawCreate T F [7;2])
    [allocation_test_bytecode 64;allocation_test_word;allocation_test_array (2 ** 59 - 3);allocation_test_word] /\
  ~ext_call_alloc_ok cenv (CreateTarget RawCreate T F [7;2])
    [allocation_test_bytecode 64;allocation_test_word;allocation_test_array (2 ** 59 - 2);allocation_test_word]
Proof
  EVAL_TAC
QED

Theorem create_blueprint_alloc_boundary_eval:
  ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T [])
    [allocation_test_word;allocation_test_word;allocation_test_word;allocation_test_array (2 ** 59 - 1)] /\
  ~ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T [])
    [allocation_test_word;allocation_test_word;allocation_test_word;allocation_test_array (2 ** 59)] /\
  ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) T F [2;3])
    [allocation_test_word;allocation_test_word;allocation_test_word;allocation_test_word;allocation_test_array (2 ** 59 - 1)] /\
  ~ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) T F [2;3])
    [allocation_test_word;allocation_test_word;allocation_test_word;allocation_test_word;allocation_test_array (2 ** 59)] /\
  ~ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T [])
    [allocation_test_word;allocation_test_word;allocation_test_word;allocation_test_array (2 ** 58);allocation_test_array (2 ** 58)]
Proof
  EVAL_TAC
QED

(* Empty, raw, fixed-buffer, and malformed cases allocate no new variable
   static constructor buffer. Their operands remain checked recursively. *)
Theorem create_alloc_nonallocating_paths_eval:
  ext_call_alloc_ok cenv (CreateTarget RawCreate F T []) [allocation_test_word;allocation_test_word] /\
  ext_call_alloc_ok cenv (CreateTarget RawCreate T T []) [allocation_test_word;allocation_test_word;allocation_test_word] /\
  ext_call_alloc_ok cenv (CreateTarget RawCreate T T []) [allocation_test_word;allocation_test_word] /\
  ext_call_alloc_ok cenv (CreateTarget RawCreate F T []) [allocation_test_word] /\
  ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) F T []) [allocation_test_word;allocation_test_word;allocation_test_word] /\
  ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint F) T T []) [allocation_test_word;allocation_test_word;allocation_test_word] /\
  ext_call_alloc_ok cenv (CreateTarget (CreateFromBlueprint T) F T [])
    [allocation_test_word;allocation_test_word;allocation_test_word;(allocation_test_array (2 ** 59))] /\
  ext_call_alloc_ok cenv (CreateTarget CreateCopyOf F T []) [allocation_test_word;allocation_test_word;(allocation_test_array (2 ** 59))] /\
  ext_call_alloc_ok cenv (CreateTarget CreateMinimalProxy F T []) [allocation_test_word;allocation_test_word;(allocation_test_array (2 ** 59))]
Proof
  EVAL_TAC
QED

(* Struct metadata can describe a large operand even when its ABI fields
   fit. CREATE checks its ABI buffer and the expression checks the operand. *)
Theorem create_alloc_struct_environment_eval:
  abi_size_bound (cenv with ce_struct_fields := FEMPTY |+ ("S", [("field", BaseT (UintT 256), 2 ** 64)])).ce_struct_fields (TupleT [expr_type (Name (StructT (NONE,"S")) "args")]) = 32 /\
  type_memory_bytes (cenv with ce_struct_fields := FEMPTY |+ ("S", [("field", BaseT (UintT 256), 2 ** 64)])) (TupleT [expr_type (Name (StructT (NONE,"S")) "args")]) = 2 ** 64 /\
  ext_call_alloc_ok (cenv with ce_struct_fields := FEMPTY |+ ("S", [("field", BaseT (UintT 256), 2 ** 64)])) (CreateTarget RawCreate F T [])
    [allocation_test_bytecode 64;allocation_test_word;Name (StructT (NONE,"S")) "args"] /\
  ext_call_alloc_ok (cenv with ce_struct_fields := FEMPTY |+ ("S", [("field", BaseT (UintT 256), 2 ** 64)])) (CreateTarget (CreateFromBlueprint F) F T [])
    [allocation_test_word;allocation_test_word;allocation_test_word;Name (StructT (NONE,"S")) "args"] /\
  ~alloc_limits_expr (cenv with ce_struct_fields := FEMPTY |+ ("S", [("field", BaseT (UintT 256), 2 ** 64)]))
    (Name (StructT (NONE,"S")) "args")
Proof
  EVAL_TAC
QED

(* Isolate the existing combined deploy guard: the raw context is accepted
   by lowering_context_ok even at the newly rejected combined endpoint.
   This exercises the generic lowering API, not a valid-source claim. *)
Theorem allocation_deploy_combined_boundary_eval:
  lowering_context_ok (install_immutable_reservation (2 ** 253)
  (FST (run_deploy_lowering_pair_compat F 0 (2 ** 253) [] 0 []
    cenv [] F F 0 F "__deploy"))) /\
  unit_alloca_budget (install_immutable_reservation (2 ** 253)
  (FST (run_deploy_lowering_pair_compat F 0 (2 ** 253) [] 0 []
    cenv [] F F 0 F "__deploy"))) = 2 ** 253 /\
  IS_SOME (run_deploy_lowering F
  ((ARB : resolved_compiler_policy) with <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize |>)
  [] (2 ** 253 - 1) [] 0 [] cenv [] F F 0 F "__deploy") /\
  run_deploy_lowering F
  ((ARB : resolved_compiler_policy) with <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear; rpol_final_assembly := FAP_Optimize |>)
  [] (2 ** 253) [] 0 [] cenv [] F F 0 F "__deploy" = NONE
Proof
  EVAL_TAC
QED
