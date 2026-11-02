(* Production-layout probe for cross-function allocation identity collisions. *)
Theory concretizePtrCollision
Ancestors concretizeMemLocDefs venomPassDispatcher venomExecSemantics
  venomFnScheduleRunner o1PassContract ptrDiscipline o1SourceUnitCheck
Libs wordsLib

Definition collision_a_def:
  collision_a = mk_raw_function "a"
    [<| bb_label := "a"; bb_instructions :=
      [mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"];
       mk_inst 100 ALLOCA [Lit (32w:256 word)] ["a_p"];
       mk_inst 101 MSTORE [Var "a_p"; Lit 0w] [];
       mk_inst 102 RET [Var "a_rpc"] []] |>]
End

Definition collision_b_def:
  collision_b = mk_raw_function "b"
    [<| bb_label := "b"; bb_instructions :=
      [mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"];
       mk_inst 100 ALLOCA [Lit (64w:256 word)] ["b_p"];
       mk_inst 103 ADD [Var "b_p"; Lit 32w] ["b_q"];
       mk_inst 104 MSTORE [Var "b_q"; Lit 1w] [];
       mk_inst 105 RET [Var "b_rpc"] []] |>]
End

Definition collision_main_def:
  collision_main = mk_raw_function "main"
    [<| bb_label := "main"; bb_instructions :=
      [mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"];
       mk_inst 2 MSTORE [Var "p"; Lit 0w] [];
       mk_inst 3 INVOKE [Label "a"] [];
       mk_inst 4 INVOKE [Label "b"] [];
       mk_inst 5 MLOAD [Var "p"] ["x"];
       mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] []] |>;
     <| bb_label := "bad"; bb_instructions :=
       [mk_inst 7 MLOAD [Lit 1024w] ["bad_x"];
        mk_inst 8 STOP [] []] |>;
     <| bb_label := "exit"; bb_instructions :=
       [mk_inst 9 STOP [] []] |>]
End

Definition collision_ctx_def:
  collision_ctx = mk_venom_context
    [collision_a; collision_b; collision_main] (SOME "main")
End

Definition collision_transform_def:
  collision_transform ctx fn = THE (concretize_function_fuel_in_context
    (concretize_memloc_fuel fn) ctx [] fn)
End

Definition collision_observed_def:
  collision_observed = mk_venom_context
    [collision_transform collision_ctx collision_a;
     collision_transform collision_ctx collision_b;
     collision_main] (SOME "main")
End

Theorem collision_leaf_layouts:
  OPTION_MAP (\f. (f.fn_eom, f.fn_mems_used))
    (concretize_function_fuel_in_context (concretize_memloc_fuel collision_a)
      collision_ctx [] collision_a) = SOME (SOME 32, [(Allocation 100,0,32)]) /\
  OPTION_MAP (\f. (f.fn_eom, f.fn_mems_used))
    (concretize_function_fuel_in_context (concretize_memloc_fuel collision_b)
      collision_ctx [] collision_b) = SOME (SOME 64, [(Allocation 100,0,64)])
Proof
  EVAL_TAC
QED

Theorem collision_imports:
  imported_mems_used collision_observed collision_main = [(Allocation 100,0,32)]
Proof
  EVAL_TAC
QED

Theorem collision_main_layout:
  OPTION_MAP (\f. (f.fn_eom, f.fn_mems_used))
    (concretize_function_fuel_in_context (concretize_memloc_fuel collision_main)
      collision_observed [] collision_main) =
    SOME (SOME 64, [(Allocation 1,32,32); (Allocation 100,0,32)])
Proof
  EVAL_TAC
QED

Definition collision_unit_def:
  collision_unit = <| cu_context := collision_observed; cu_data_segment := [] |>
End

Definition collision_later_def:
  collision_later fn = run_configured_fn_pass_fold execute_configured_fn_pass
    ARB (DROP 3 o1_fn_passes) collision_unit (init_ir_supply collision_unit)
    (collision_transform collision_ctx fn) []
End

Theorem collision_a_exact:
  collision_transform collision_ctx collision_a =
    (mk_raw_function "a"
      [<| bb_label := "a"; bb_instructions :=
        [mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"];
         mk_inst 100 ASSIGN [Lit (0w:256 word)] ["a_p"];
         mk_inst 101 MSTORE [Var "a_p"; Lit 0w] [];
         mk_inst 102 RET [Var "a_rpc"] []] |>]) with
      <| fn_eom := SOME 32; fn_mems_used := [(Allocation 100,0,32)] |>
Proof
  EVAL_TAC
QED

Theorem collision_b_exact:
  collision_transform collision_ctx collision_b =
    (mk_raw_function "b"
      [<| bb_label := "b"; bb_instructions :=
        [mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"];
         mk_inst 100 ASSIGN [Lit (0w:256 word)] ["b_p"];
         mk_inst 103 ADD [Var "b_p"; Lit 32w] ["b_q"];
         mk_inst 104 MSTORE [Var "b_q"; Lit 1w] [];
         mk_inst 105 RET [Var "b_rpc"] []] |>]) with
      <| fn_eom := SOME 64; fn_mems_used := [(Allocation 100,0,64)] |>
Proof
  EVAL_TAC
QED

Theorem collision_return_prefixes:
  canonical_param_prefix collision_a /\ canonical_param_prefix collision_b
Proof
  EVAL_TAC
QED


Definition collision_sealed_def:
  collision_sealed fn = (collision_transform collision_ctx fn) with
    fn_fmp_signature := SOME <| fms_has_fmp_param := F; fms_publishes := F |>
End

Theorem collision_fmp_exact:
  execute_configured_fn_pass ARB (CFP_Simple VP_FmpLowering)
    collision_unit (init_ir_supply collision_unit)
    (collision_transform collision_ctx collision_a) =
      SOME <| fpo_function := collision_sealed collision_a;
              fpo_label_map := []; fpo_supply := init_ir_supply collision_unit |> /\
  execute_configured_fn_pass ARB (CFP_Simple VP_FmpLowering)
    collision_unit (init_ir_supply collision_unit)
    (collision_transform collision_ctx collision_b) =
      SOME <| fpo_function := collision_sealed collision_b;
              fpo_label_map := []; fpo_supply := init_ir_supply collision_unit |>
Proof
  rewrite_tac[collision_sealed_def, collision_unit_def, collision_observed_def,
    collision_a_exact, collision_b_exact] >>
  conj_tac >> EVAL_TAC >> simp[finite_mapTheory.FEVERY_DEF]
QED

Theorem collision_seals_valid:
  fmp_signature_syntax_wf
    <| fms_has_fmp_param := F; fms_publishes := F |> (collision_sealed collision_a) /\
  fmp_signature_syntax_wf
    <| fms_has_fmp_param := F; fms_publishes := F |> (collision_sealed collision_b)
Proof
  rewrite_tac[collision_sealed_def, collision_a_exact, collision_b_exact] >> EVAL_TAC
QED

Theorem collision_zero_user_returns:
  fmp_unique_return_arity
    <| fms_has_fmp_param := F; fms_publishes := F |> collision_a = SOME 0 /\
  fmp_unique_return_arity
    <| fms_has_fmp_param := F; fms_publishes := F |> collision_b = SOME 0
Proof
  EVAL_TAC
QED

Definition collision_current_unit_def:
  collision_current_unit fn = collision_unit with cu_context :=
    collision_observed with ctx_functions :=
      MAP (\f. if f.fn_name = fn.fn_name then fn else f)
        collision_observed.ctx_functions
End

Theorem collision_ssa_exact:
  !fn. MEM fn [collision_a; collision_b] ==>
  execute_configured_fn_pass ARB (CFP_Simple VP_MakeSSA)
    (collision_current_unit (collision_sealed fn))
    (init_ir_supply collision_unit) (collision_sealed fn) =
      SOME <| fpo_function := collision_sealed fn;
              fpo_label_map := []; fpo_supply := init_ir_supply collision_unit |>
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[collision_current_unit_def, collision_sealed_def,
    collision_unit_def, collision_observed_def, collision_a_exact,
    collision_b_exact] >> EVAL_TAC
QED

Theorem collision_simplify_exact:
  !fn. MEM fn [collision_a; collision_b] ==>
  execute_configured_fn_pass ARB (CFP_Simple VP_SimplifyCFG)
    (collision_current_unit (collision_sealed fn))
    (init_ir_supply collision_unit) (collision_sealed fn) =
      SOME <| fpo_function := collision_sealed fn;
              fpo_label_map := []; fpo_supply := init_ir_supply collision_unit |>
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[collision_current_unit_def, collision_sealed_def,
    collision_unit_def, collision_observed_def, collision_a_exact,
    collision_b_exact] >> EVAL_TAC
QED

Definition collision_expanded_def:
  collision_expanded fn = (collision_sealed fn) with fn_blocks :=
    if fn = collision_a then
      [<| bb_label := "a"; bb_instructions :=
        [mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"];
         mk_inst 100 ASSIGN [Lit 0w] ["a_p"];
         mk_inst 108 ASSIGN [Lit 0w] ["formal_var_0"];
         mk_inst 101 MSTORE [Var "a_p"; Var "formal_var_0"] [];
         mk_inst 102 RET [Var "a_rpc"] []] |>]
    else
      [<| bb_label := "b"; bb_instructions :=
        [mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"];
         mk_inst 100 ASSIGN [Lit 0w] ["b_p"];
         mk_inst 108 ASSIGN [Lit 32w] ["formal_var_0"];
         mk_inst 103 ADD [Var "b_p"; Var "formal_var_0"] ["b_q"];
         mk_inst 109 ASSIGN [Lit 1w] ["formal_var_1"];
         mk_inst 104 MSTORE [Var "b_q"; Var "formal_var_1"] [];
         mk_inst 105 RET [Var "b_rpc"] []] |>]
End

Definition collision_expanded_supply_def:
  collision_expanded_supply fn = (init_ir_supply collision_unit) with
    <| irs_next_inst := if fn = collision_a then 109 else 110;
       irs_next_var := if fn = collision_a then 1 else 2;
       irs_used_inst_ids := (if fn = collision_a then [108] else [109;108]) ++
         (init_ir_supply collision_unit).irs_used_inst_ids;
       irs_used_vars :=
         (if fn = collision_a then ["formal_var_0"] else ["formal_var_1";"formal_var_0"]) ++
         (init_ir_supply collision_unit).irs_used_vars |>
End

Theorem collision_expansion_exact:
  !fn. MEM fn [collision_a; collision_b] ==>
  execute_configured_fn_pass ARB (CFP_Simple VP_SingleUseExpansion)
    (collision_current_unit (collision_sealed fn))
    (init_ir_supply collision_unit) (collision_sealed fn) =
      SOME <| fpo_function := collision_expanded fn;
              fpo_label_map := []; fpo_supply := collision_expanded_supply fn |>
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[collision_expanded_def, collision_expanded_supply_def,
    collision_current_unit_def, collision_sealed_def,
    collision_unit_def, collision_observed_def, collision_a_exact,
    collision_b_exact] >> EVAL_TAC
QED

Definition collision_scheduled_def:
  collision_scheduled fn = (collision_expanded fn) with fn_blocks :=
    [<| bb_label := fn.fn_name; bb_instructions :=
      MAP (\i. EL i (HD (collision_expanded fn).fn_blocks).bb_instructions)
        (if fn = collision_a then [0;2;1;3;4] else [0;4;2;1;3;5;6]) |>]
End

Theorem collision_dft_exact:
  !fn. MEM fn [collision_a; collision_b] ==>
  execute_configured_fn_pass ARB (CFP_Simple VP_DFT)
    (collision_current_unit (collision_expanded fn))
    (collision_expanded_supply fn) (collision_expanded fn) =
      SOME <| fpo_function := collision_scheduled fn;
              fpo_label_map := []; fpo_supply := collision_expanded_supply fn |>
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[collision_scheduled_def, collision_expanded_def,
    collision_expanded_supply_def, collision_current_unit_def, collision_sealed_def,
    collision_unit_def, collision_observed_def, collision_a_exact,
    collision_b_exact] >> EVAL_TAC
QED

Theorem collision_normalization_exact:
  !fn. MEM fn [collision_a; collision_b] ==>
  execute_configured_fn_pass ARB (CFP_Simple VP_CFGNormalization)
    (collision_current_unit (collision_scheduled fn))
    (collision_expanded_supply fn) (collision_scheduled fn) =
      SOME <| fpo_function := collision_scheduled fn;
              fpo_label_map := []; fpo_supply := collision_expanded_supply fn |>
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  rewrite_tac[collision_scheduled_def, collision_expanded_def,
    collision_expanded_supply_def, collision_current_unit_def, collision_sealed_def,
    collision_unit_def, collision_observed_def, collision_a_exact,
    collision_b_exact] >> EVAL_TAC
QED

Theorem collision_final_metadata:
  (collision_scheduled collision_a).fn_mems_used = [(Allocation 100,0,32)] /\
  (collision_scheduled collision_a).fn_eom = SOME 32 /\
  (collision_scheduled collision_b).fn_mems_used = [(Allocation 100,0,64)] /\
  (collision_scheduled collision_b).fn_eom = SOME 64
Proof
  rewrite_tac[collision_scheduled_def, collision_expanded_def,
    collision_sealed_def, collision_a_exact, collision_b_exact] >> EVAL_TAC
QED

Definition collision_finished_ctx_def:
  collision_finished_ctx = mk_venom_context
    [collision_scheduled collision_a; collision_scheduled collision_b;
     collision_main] (SOME "main")
End

Theorem collision_finished_layout:
  imported_mems_used collision_finished_ctx collision_main = [(Allocation 100,0,32)] /\
  OPTION_MAP (\f. (f.fn_eom, f.fn_mems_used))
    (concretize_function_fuel_in_context (concretize_memloc_fuel collision_main)
      collision_finished_ctx [] collision_main) =
    SOME (SOME 64, [(Allocation 1,32,32); (Allocation 100,0,32)])
Proof
  EVAL_TAC
QED

Definition collision_output_ctx_def:
  collision_output_ctx = collision_finished_ctx with ctx_functions :=
    [collision_transform collision_ctx collision_a;
     collision_transform collision_ctx collision_b;
     collision_transform collision_finished_ctx collision_main]
End


Definition collision_start_def:
  collision_start = init_venom_state "main"
End

Definition collision_raw_allocated_def:
  collision_raw_allocated = collision_start with
    <| vs_vars := FEMPTY |+ ("p",(0w:256 word));
       vs_allocas := FEMPTY |+ (1,(0,32)); vs_alloca_next := 32 |>
End

Definition collision_raw_call_a_def:
  collision_raw_call_a = collision_raw_allocated with
    <| vs_memory := REPLICATE 32 (0w:8 word); vs_inst_idx := 2 |>
End

Definition collision_packed_allocated_def:
  collision_packed_allocated = collision_start with
    vs_vars := FEMPTY |+ ("p",(32w:256 word))
End

Definition collision_packed_call_a_def:
  collision_packed_call_a = collision_packed_allocated with
    <| vs_memory := REPLICATE 64 (0w:8 word); vs_inst_idx := 2 |>
End

Theorem collision_initial_allocations:
  step_inst_base (mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"])
    collision_start = OK collision_raw_allocated /\
  step_inst_base (mk_inst 1 ASSIGN [Lit (32w:256 word)] ["p"])
    collision_start = OK collision_packed_allocated
Proof
  EVAL_TAC
QED

Theorem collision_initial_stores:
  step_inst_base (mk_inst 2 MSTORE [Var "p"; Lit (0w:256 word)] [])
    (collision_raw_allocated with vs_inst_idx := 1) =
      OK (collision_raw_call_a with vs_inst_idx := 1) /\
  step_inst_base (mk_inst 2 MSTORE [Var "p"; Lit (0w:256 word)] [])
    (collision_packed_allocated with vs_inst_idx := 1) =
      OK (collision_packed_call_a with vs_inst_idx := 1)
Proof
  EVAL_TAC
QED

Definition collision_raw_a_entry_def:
  collision_raw_a_entry = collision_raw_call_a with
    <| vs_vars := FEMPTY; vs_current_bb := "a"; vs_inst_idx := 0;
       vs_allocas := FEMPTY |>
End

Definition collision_raw_a_rpc_def:
  collision_raw_a_rpc = collision_raw_a_entry with
    vs_vars := FEMPTY |+ ("a_rpc",(0w:256 word))
End

Definition collision_raw_a_allocated_def:
  collision_raw_a_allocated = collision_raw_a_rpc with
    <| vs_vars := FEMPTY |+ ("a_rpc",(0w:256 word)) |+ ("a_p",32w);
       vs_allocas := FEMPTY |+ (100,(32,32));
       vs_alloca_next := 64; vs_inst_idx := 1 |>
End

Definition collision_raw_a_stored_def:
  collision_raw_a_stored = collision_raw_a_allocated with
    <| vs_memory := REPLICATE 64 (0w:8 word); vs_inst_idx := 2 |>
End

Theorem collision_raw_a_setup:
  setup_callee collision_a [] collision_raw_call_a = SOME collision_raw_a_entry
Proof
  EVAL_TAC
QED

Theorem collision_raw_a_steps:
  step_inst_base (mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"])
    collision_raw_a_entry = OK collision_raw_a_rpc /\
  step_inst_base (mk_inst 100 ALLOCA [Lit (32w:256 word)] ["a_p"])
    (collision_raw_a_rpc with vs_inst_idx := 1) = OK collision_raw_a_allocated /\
  step_inst_base (mk_inst 101 MSTORE [Var "a_p"; Lit (0w:256 word)] [])
    (collision_raw_a_allocated with vs_inst_idx := 2) = OK collision_raw_a_stored /\
  step_inst_base (mk_inst 102 RET [Var "a_rpc"] [])
    (collision_raw_a_stored with vs_inst_idx := 3) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_raw_a_stored with vs_inst_idx := 3)
Proof
  EVAL_TAC
QED

Definition collision_raw_a_bb_def:
  collision_raw_a_bb = <| bb_label := "a"; bb_instructions :=
    [mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"];
     mk_inst 100 ALLOCA [Lit 32w] ["a_p"];
     mk_inst 101 MSTORE [Var "a_p"; Lit 0w] [];
     mk_inst 102 RET [Var "a_rpc"] []] |>
End

Theorem collision_raw_a_indices[local]:
  collision_raw_a_entry.vs_inst_idx = 0 /\
  collision_raw_a_rpc.vs_inst_idx = 0 /\
  collision_raw_a_allocated.vs_inst_idx = 1 /\
  collision_raw_a_stored.vs_inst_idx = 2 /\
  ~collision_raw_a_rpc.vs_halted /\
  ~collision_raw_a_allocated.vs_halted /\
  ~collision_raw_a_stored.vs_halted
Proof
  EVAL_TAC
QED

Theorem collision_raw_a_step_lift[local]:
  !fuel ctx.
  step_inst fuel ctx (mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"])
    collision_raw_a_entry = OK collision_raw_a_rpc /\
  step_inst fuel ctx (mk_inst 100 ALLOCA [Lit (32w:256 word)] ["a_p"])
    (collision_raw_a_rpc with vs_inst_idx := 1) = OK collision_raw_a_allocated /\
  step_inst fuel ctx (mk_inst 101 MSTORE [Var "a_p"; Lit (0w:256 word)] [])
    (collision_raw_a_allocated with vs_inst_idx := 2) = OK collision_raw_a_stored /\
  step_inst fuel ctx (mk_inst 102 RET [Var "a_rpc"] [])
    (collision_raw_a_stored with vs_inst_idx := 3) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_raw_a_stored with vs_inst_idx := 3)
Proof
  rpt gen_tac >>
  once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_a_steps]
QED

Theorem collision_raw_a_block:
  !fuel ctx.
  exec_block fuel ctx collision_raw_a_bb collision_raw_a_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_raw_a_stored with vs_inst_idx := 3)
Proof
  rpt gen_tac >>
  ntac 4 (simp[Once exec_block_def, collision_raw_a_bb_def,
    venomInstTheory.get_instruction_def, collision_raw_a_indices,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_a_step_lift,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def])
QED

Theorem collision_raw_a_entry_facts[local]:
  lookup_block collision_raw_a_entry.vs_current_bb collision_a.fn_blocks =
    SOME collision_raw_a_bb /\
  eval_phis collision_raw_a_entry collision_raw_a_bb.bb_instructions =
    OK collision_raw_a_entry /\
  phi_prefix_length collision_raw_a_bb.bb_instructions = 0 /\
  (collision_raw_a_entry with vs_inst_idx := 0) = collision_raw_a_entry
Proof
  EVAL_TAC
QED

Theorem collision_raw_a_run:
  !fuel ctx.
  run_blocks (SUC fuel) ctx collision_a collision_raw_a_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_raw_a_stored with vs_inst_idx := 3)
Proof
  rpt gen_tac >>
  once_rewrite_tac[run_blocks_def] >>
  simp[collision_raw_a_entry_facts, collision_raw_a_block]
QED

Definition collision_raw_call_b_def:
  collision_raw_call_b = collision_raw_call_a with
    <| vs_memory := REPLICATE 64 (0w:8 word); vs_inst_idx := 3 |>
End

Theorem collision_raw_a_return_merge[local]:
  bind_outputs [] []
    (adopt_return_fmp <| iret_values := []; iret_adopt_fmp := NONE |>
      (merge_callee_state collision_raw_call_a
        (collision_raw_a_stored with vs_inst_idx := 3))) =
    SOME (collision_raw_call_b with vs_inst_idx := 2)
Proof
  EVAL_TAC
QED

Theorem collision_raw_a_call_facts[local]:
  decode_invoke (mk_inst 3 INVOKE [Label "a"] []) = SOME ("a",[]) /\
  lookup_function "a" collision_ctx.ctx_functions = SOME collision_a /\
  eval_operands [] collision_raw_call_a = SOME []
Proof
  EVAL_TAC
QED

Theorem collision_raw_a_invoke:
  !fuel.
  step_inst (SUC fuel) collision_ctx (mk_inst 3 INVOKE [Label "a"] [])
    collision_raw_call_a = OK (collision_raw_call_b with vs_inst_idx := 2)
Proof
  gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_a_call_facts,
    collision_raw_a_setup, collision_raw_a_run, SRULE [] collision_raw_a_return_merge]
QED

Definition collision_raw_b_entry_def:
  collision_raw_b_entry = collision_raw_call_b with
    <| vs_vars := FEMPTY; vs_current_bb := "b"; vs_inst_idx := 0;
       vs_allocas := FEMPTY |>
End

Definition collision_raw_b_rpc_def:
  collision_raw_b_rpc = collision_raw_b_entry with
    vs_vars := FEMPTY |+ ("b_rpc",(0w:256 word))
End

Definition collision_raw_b_allocated_def:
  collision_raw_b_allocated = collision_raw_b_rpc with
    <| vs_vars := FEMPTY |+ ("b_rpc",(0w:256 word)) |+ ("b_p",32w);
       vs_allocas := FEMPTY |+ (100,(32,64));
       vs_alloca_next := 96; vs_inst_idx := 1 |>
End

Definition collision_raw_b_added_def:
  collision_raw_b_added = collision_raw_b_allocated with
    <| vs_vars := FEMPTY |+ ("b_rpc",(0w:256 word)) |+ ("b_p",32w)
                        |+ ("b_q",64w); vs_inst_idx := 2 |>
End

Definition collision_raw_b_stored_def:
  collision_raw_b_stored = collision_raw_b_added with
    <| vs_memory := REPLICATE 95 (0w:8 word) ++ [1w]; vs_inst_idx := 3 |>
End

Theorem collision_raw_b_setup:
  setup_callee collision_b [] collision_raw_call_b = SOME collision_raw_b_entry
Proof
  EVAL_TAC
QED

Theorem collision_raw_b_steps:
  step_inst_base (mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"])
    collision_raw_b_entry = OK collision_raw_b_rpc /\
  step_inst_base (mk_inst 100 ALLOCA [Lit (64w:256 word)] ["b_p"])
    (collision_raw_b_rpc with vs_inst_idx := 1) = OK collision_raw_b_allocated /\
  step_inst_base (mk_inst 103 ADD [Var "b_p"; Lit (32w:256 word)] ["b_q"])
    (collision_raw_b_allocated with vs_inst_idx := 2) = OK collision_raw_b_added /\
  step_inst_base (mk_inst 104 MSTORE [Var "b_q"; Lit (1w:256 word)] [])
    (collision_raw_b_added with vs_inst_idx := 3) = OK collision_raw_b_stored /\
  step_inst_base (mk_inst 105 RET [Var "b_rpc"] [])
    (collision_raw_b_stored with vs_inst_idx := 4) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_raw_b_stored with vs_inst_idx := 4)
Proof
  EVAL_TAC
QED

Definition collision_raw_b_bb_def:
  collision_raw_b_bb = <| bb_label := "b"; bb_instructions :=
    [mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"];
     mk_inst 100 ALLOCA [Lit 64w] ["b_p"];
     mk_inst 103 ADD [Var "b_p"; Lit 32w] ["b_q"];
     mk_inst 104 MSTORE [Var "b_q"; Lit 1w] [];
     mk_inst 105 RET [Var "b_rpc"] []] |>
End

Theorem collision_raw_b_indices[local]:
  collision_raw_b_entry.vs_inst_idx = 0 /\
  collision_raw_b_rpc.vs_inst_idx = 0 /\
  collision_raw_b_allocated.vs_inst_idx = 1 /\
  collision_raw_b_added.vs_inst_idx = 2 /\
  collision_raw_b_stored.vs_inst_idx = 3 /\
  ~collision_raw_b_rpc.vs_halted /\
  ~collision_raw_b_allocated.vs_halted /\
  ~collision_raw_b_added.vs_halted /\
  ~collision_raw_b_stored.vs_halted
Proof
  EVAL_TAC
QED

Theorem collision_raw_b_step_lift[local]:
  !fuel ctx.
  step_inst fuel ctx (mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"])
    collision_raw_b_entry = OK collision_raw_b_rpc /\
  step_inst fuel ctx (mk_inst 100 ALLOCA [Lit (64w:256 word)] ["b_p"])
    (collision_raw_b_rpc with vs_inst_idx := 1) = OK collision_raw_b_allocated /\
  step_inst fuel ctx (mk_inst 103 ADD [Var "b_p"; Lit (32w:256 word)] ["b_q"])
    (collision_raw_b_allocated with vs_inst_idx := 2) = OK collision_raw_b_added /\
  step_inst fuel ctx (mk_inst 104 MSTORE [Var "b_q"; Lit (1w:256 word)] [])
    (collision_raw_b_added with vs_inst_idx := 3) = OK collision_raw_b_stored /\
  step_inst fuel ctx (mk_inst 105 RET [Var "b_rpc"] [])
    (collision_raw_b_stored with vs_inst_idx := 4) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_raw_b_stored with vs_inst_idx := 4)
Proof
  rpt gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_b_steps]
QED

Theorem collision_raw_b_block:
  !fuel ctx.
  exec_block fuel ctx collision_raw_b_bb collision_raw_b_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_raw_b_stored with vs_inst_idx := 4)
Proof
  rpt gen_tac >>
  ntac 5 (simp[Once exec_block_def, collision_raw_b_bb_def,
    venomInstTheory.get_instruction_def, collision_raw_b_indices,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_b_step_lift,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def])
QED

Theorem collision_raw_b_entry_facts[local]:
  lookup_block collision_raw_b_entry.vs_current_bb collision_b.fn_blocks =
    SOME collision_raw_b_bb /\
  eval_phis collision_raw_b_entry collision_raw_b_bb.bb_instructions =
    OK collision_raw_b_entry /\
  phi_prefix_length collision_raw_b_bb.bb_instructions = 0 /\
  (collision_raw_b_entry with vs_inst_idx := 0) = collision_raw_b_entry
Proof
  EVAL_TAC
QED

Theorem collision_raw_b_run:
  !fuel ctx.
  run_blocks (SUC fuel) ctx collision_b collision_raw_b_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_raw_b_stored with vs_inst_idx := 4)
Proof
  rpt gen_tac >> once_rewrite_tac[run_blocks_def] >>
  simp[collision_raw_b_entry_facts, collision_raw_b_block]
QED

Definition collision_raw_load_def:
  collision_raw_load = collision_raw_call_b with
    <| vs_memory := REPLICATE 95 (0w:8 word) ++ [1w]; vs_inst_idx := 4 |>
End

Theorem collision_raw_b_return_merge[local]:
  bind_outputs [] []
    (adopt_return_fmp <| iret_values := []; iret_adopt_fmp := NONE |>
      (merge_callee_state collision_raw_call_b
        (collision_raw_b_stored with vs_inst_idx := 4))) =
    SOME (collision_raw_load with vs_inst_idx := 3)
Proof
  EVAL_TAC
QED

Theorem collision_raw_b_call_facts[local]:
  decode_invoke (mk_inst 4 INVOKE [Label "b"] []) = SOME ("b",[]) /\
  lookup_function "b" collision_ctx.ctx_functions = SOME collision_b /\
  eval_operands [] collision_raw_call_b = SOME []
Proof
  EVAL_TAC
QED

Theorem collision_raw_b_invoke:
  !fuel.
  step_inst (SUC fuel) collision_ctx (mk_inst 4 INVOKE [Label "b"] [])
    collision_raw_call_b = OK (collision_raw_load with vs_inst_idx := 3)
Proof
  gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_b_call_facts,
    collision_raw_b_setup, collision_raw_b_run, SRULE [] collision_raw_b_return_merge]
QED

Definition collision_packed_a_entry_def:
  collision_packed_a_entry = collision_packed_call_a with
    <| vs_vars := FEMPTY; vs_current_bb := "a"; vs_inst_idx := 0;
       vs_allocas := FEMPTY |>
End

Definition collision_packed_a_rpc_def:
  collision_packed_a_rpc = collision_packed_a_entry with
    vs_vars := FEMPTY |+ ("a_rpc",(0w:256 word))
End

Definition collision_packed_a_assigned_def:
  collision_packed_a_assigned = collision_packed_a_rpc with
    <| vs_vars := FEMPTY |+ ("a_rpc",(0w:256 word)) |+ ("a_p",0w);
       vs_inst_idx := 1 |>
End

Definition collision_packed_a_stored_def:
  collision_packed_a_stored = collision_packed_a_assigned with vs_inst_idx := 2
End

Theorem collision_packed_a_setup:
  setup_callee (collision_transform collision_ctx collision_a) [] collision_packed_call_a =
    SOME collision_packed_a_entry
Proof
  EVAL_TAC
QED

Theorem collision_packed_a_steps:
  step_inst_base (mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"])
    collision_packed_a_entry = OK collision_packed_a_rpc /\
  step_inst_base (mk_inst 100 ASSIGN [Lit (0w:256 word)] ["a_p"])
    (collision_packed_a_rpc with vs_inst_idx := 1) = OK collision_packed_a_assigned /\
  step_inst_base (mk_inst 101 MSTORE [Var "a_p"; Lit (0w:256 word)] [])
    (collision_packed_a_assigned with vs_inst_idx := 2) = OK collision_packed_a_stored /\
  step_inst_base (mk_inst 102 RET [Var "a_rpc"] [])
    (collision_packed_a_stored with vs_inst_idx := 3) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_packed_a_stored with vs_inst_idx := 3)
Proof
  EVAL_TAC
QED

Definition collision_packed_a_bb_def:
  collision_packed_a_bb = <| bb_label := "a"; bb_instructions :=
    [mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"];
     mk_inst 100 ASSIGN [Lit 0w] ["a_p"];
     mk_inst 101 MSTORE [Var "a_p"; Lit 0w] [];
     mk_inst 102 RET [Var "a_rpc"] []] |>
End

Theorem collision_packed_a_indices[local]:
  collision_packed_a_entry.vs_inst_idx = 0 /\
  collision_packed_a_rpc.vs_inst_idx = 0 /\
  collision_packed_a_assigned.vs_inst_idx = 1 /\
  collision_packed_a_stored.vs_inst_idx = 2
Proof
  EVAL_TAC
QED

Theorem collision_packed_a_step_lift[local]:
  !fuel ctx.
  step_inst fuel ctx (mk_inst 106 RETPC_PARAM [Lit (0w:256 word)] ["a_rpc"])
    collision_packed_a_entry = OK collision_packed_a_rpc /\
  step_inst fuel ctx (mk_inst 100 ASSIGN [Lit (0w:256 word)] ["a_p"])
    (collision_packed_a_rpc with vs_inst_idx := 1) = OK collision_packed_a_assigned /\
  step_inst fuel ctx (mk_inst 101 MSTORE [Var "a_p"; Lit (0w:256 word)] [])
    (collision_packed_a_assigned with vs_inst_idx := 2) = OK collision_packed_a_stored /\
  step_inst fuel ctx (mk_inst 102 RET [Var "a_rpc"] [])
    (collision_packed_a_stored with vs_inst_idx := 3) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_packed_a_stored with vs_inst_idx := 3)
Proof
  rpt gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_a_steps]
QED

Theorem collision_packed_a_block:
  !fuel ctx.
  exec_block fuel ctx collision_packed_a_bb collision_packed_a_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_packed_a_stored with vs_inst_idx := 3)
Proof
  rpt gen_tac >>
  ntac 4 (simp[Once exec_block_def, collision_packed_a_bb_def,
    venomInstTheory.get_instruction_def, collision_packed_a_indices,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_a_step_lift,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def])
QED

Theorem collision_packed_a_entry_facts[local]:
  lookup_block collision_packed_a_entry.vs_current_bb
    (collision_transform collision_ctx collision_a).fn_blocks = SOME collision_packed_a_bb /\
  eval_phis collision_packed_a_entry collision_packed_a_bb.bb_instructions =
    OK collision_packed_a_entry /\
  phi_prefix_length collision_packed_a_bb.bb_instructions = 0 /\
  (collision_packed_a_entry with vs_inst_idx := 0) = collision_packed_a_entry
Proof
  EVAL_TAC
QED

Theorem collision_packed_a_run:
  !fuel ctx.
  run_blocks (SUC fuel) ctx (collision_transform collision_ctx collision_a) collision_packed_a_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_packed_a_stored with vs_inst_idx := 3)
Proof
  rpt gen_tac >> once_rewrite_tac[run_blocks_def] >>
  simp[collision_packed_a_entry_facts, collision_packed_a_block]
QED

Definition collision_packed_call_b_def:
  collision_packed_call_b = collision_packed_call_a with vs_inst_idx := 3
End

Theorem collision_packed_a_return_merge[local]:
  bind_outputs [] []
    (adopt_return_fmp <| iret_values := []; iret_adopt_fmp := NONE |>
      (merge_callee_state collision_packed_call_a
        (collision_packed_a_stored with vs_inst_idx := 3))) =
    SOME (collision_packed_call_b with vs_inst_idx := 2)
Proof
  EVAL_TAC
QED

Theorem collision_packed_a_call_facts[local]:
  decode_invoke (mk_inst 3 INVOKE [Label "a"] []) = SOME ("a",[]) /\
  lookup_function "a" collision_output_ctx.ctx_functions =
    SOME (collision_transform collision_ctx collision_a) /\
  eval_operands [] collision_packed_call_a = SOME []
Proof
  EVAL_TAC
QED

Theorem collision_packed_a_invoke:
  !fuel.
  step_inst (SUC fuel) collision_output_ctx (mk_inst 3 INVOKE [Label "a"] [])
    collision_packed_call_a = OK (collision_packed_call_b with vs_inst_idx := 2)
Proof
  gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_a_call_facts,
    collision_packed_a_setup, collision_packed_a_run,
    SRULE [] collision_packed_a_return_merge]
QED

Definition collision_packed_b_entry_def:
  collision_packed_b_entry = collision_packed_call_b with
    <| vs_vars := FEMPTY; vs_current_bb := "b"; vs_inst_idx := 0;
       vs_allocas := FEMPTY |>
End

Definition collision_packed_b_rpc_def:
  collision_packed_b_rpc = collision_packed_b_entry with
    vs_vars := FEMPTY |+ ("b_rpc",(0w:256 word))
End

Definition collision_packed_b_assigned_def:
  collision_packed_b_assigned = collision_packed_b_rpc with
    <| vs_vars := FEMPTY |+ ("b_rpc",(0w:256 word)) |+ ("b_p",0w);
       vs_inst_idx := 1 |>
End

Definition collision_packed_b_added_def:
  collision_packed_b_added = collision_packed_b_assigned with
    <| vs_vars := FEMPTY |+ ("b_rpc",(0w:256 word)) |+ ("b_p",0w) |+ ("b_q",32w);
       vs_inst_idx := 2 |>
End

Definition collision_packed_b_stored_def:
  collision_packed_b_stored = collision_packed_b_added with
    <| vs_memory := REPLICATE 63 (0w:8 word) ++ [1w]; vs_inst_idx := 3 |>
End

Theorem collision_packed_b_setup:
  setup_callee (collision_transform collision_ctx collision_b) [] collision_packed_call_b =
    SOME collision_packed_b_entry
Proof
  EVAL_TAC
QED

Theorem collision_packed_b_steps:
  step_inst_base (mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"])
    collision_packed_b_entry = OK collision_packed_b_rpc /\
  step_inst_base (mk_inst 100 ASSIGN [Lit (0w:256 word)] ["b_p"])
    (collision_packed_b_rpc with vs_inst_idx := 1) = OK collision_packed_b_assigned /\
  step_inst_base (mk_inst 103 ADD [Var "b_p"; Lit (32w:256 word)] ["b_q"])
    (collision_packed_b_assigned with vs_inst_idx := 2) = OK collision_packed_b_added /\
  step_inst_base (mk_inst 104 MSTORE [Var "b_q"; Lit (1w:256 word)] [])
    (collision_packed_b_added with vs_inst_idx := 3) = OK collision_packed_b_stored /\
  step_inst_base (mk_inst 105 RET [Var "b_rpc"] [])
    (collision_packed_b_stored with vs_inst_idx := 4) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_packed_b_stored with vs_inst_idx := 4)
Proof
  EVAL_TAC
QED

Definition collision_packed_b_bb_def:
  collision_packed_b_bb = <| bb_label := "b"; bb_instructions :=
    [mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"];
     mk_inst 100 ASSIGN [Lit 0w] ["b_p"];
     mk_inst 103 ADD [Var "b_p"; Lit 32w] ["b_q"];
     mk_inst 104 MSTORE [Var "b_q"; Lit 1w] [];
     mk_inst 105 RET [Var "b_rpc"] []] |>
End

Theorem collision_packed_b_indices[local]:
  collision_packed_b_entry.vs_inst_idx = 0 /\
  collision_packed_b_rpc.vs_inst_idx = 0 /\
  collision_packed_b_assigned.vs_inst_idx = 1 /\
  collision_packed_b_added.vs_inst_idx = 2 /\
  collision_packed_b_stored.vs_inst_idx = 3
Proof
  EVAL_TAC
QED

Theorem collision_packed_b_step_lift[local]:
  !fuel ctx.
  step_inst fuel ctx (mk_inst 107 RETPC_PARAM [Lit (0w:256 word)] ["b_rpc"])
    collision_packed_b_entry = OK collision_packed_b_rpc /\
  step_inst fuel ctx (mk_inst 100 ASSIGN [Lit (0w:256 word)] ["b_p"])
    (collision_packed_b_rpc with vs_inst_idx := 1) = OK collision_packed_b_assigned /\
  step_inst fuel ctx (mk_inst 103 ADD [Var "b_p"; Lit (32w:256 word)] ["b_q"])
    (collision_packed_b_assigned with vs_inst_idx := 2) = OK collision_packed_b_added /\
  step_inst fuel ctx (mk_inst 104 MSTORE [Var "b_q"; Lit (1w:256 word)] [])
    (collision_packed_b_added with vs_inst_idx := 3) = OK collision_packed_b_stored /\
  step_inst fuel ctx (mk_inst 105 RET [Var "b_rpc"] [])
    (collision_packed_b_stored with vs_inst_idx := 4) =
      IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
        (collision_packed_b_stored with vs_inst_idx := 4)
Proof
  rpt gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_b_steps]
QED

Theorem collision_packed_b_block:
  !fuel ctx.
  exec_block fuel ctx collision_packed_b_bb collision_packed_b_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_packed_b_stored with vs_inst_idx := 4)
Proof
  rpt gen_tac >>
  ntac 5 (simp[Once exec_block_def, collision_packed_b_bb_def,
    venomInstTheory.get_instruction_def, collision_packed_b_indices,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_b_step_lift,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def])
QED

Theorem collision_packed_b_entry_facts[local]:
  lookup_block collision_packed_b_entry.vs_current_bb
    (collision_transform collision_ctx collision_b).fn_blocks = SOME collision_packed_b_bb /\
  eval_phis collision_packed_b_entry collision_packed_b_bb.bb_instructions =
    OK collision_packed_b_entry /\
  phi_prefix_length collision_packed_b_bb.bb_instructions = 0 /\
  (collision_packed_b_entry with vs_inst_idx := 0) = collision_packed_b_entry
Proof
  EVAL_TAC
QED

Theorem collision_packed_b_run:
  !fuel ctx.
  run_blocks (SUC fuel) ctx (collision_transform collision_ctx collision_b) collision_packed_b_entry =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |>
      (collision_packed_b_stored with vs_inst_idx := 4)
Proof
  rpt gen_tac >> once_rewrite_tac[run_blocks_def] >>
  simp[collision_packed_b_entry_facts, collision_packed_b_block]
QED

Definition collision_packed_load_def:
  collision_packed_load = collision_packed_call_b with
    <| vs_memory := REPLICATE 63 (0w:8 word) ++ [1w]; vs_inst_idx := 4 |>
End

Theorem collision_packed_b_return_merge[local]:
  bind_outputs [] []
    (adopt_return_fmp <| iret_values := []; iret_adopt_fmp := NONE |>
      (merge_callee_state collision_packed_call_b
        (collision_packed_b_stored with vs_inst_idx := 4))) =
    SOME (collision_packed_load with vs_inst_idx := 3)
Proof
  EVAL_TAC
QED

Theorem collision_packed_b_call_facts[local]:
  decode_invoke (mk_inst 4 INVOKE [Label "b"] []) = SOME ("b",[]) /\
  lookup_function "b" collision_output_ctx.ctx_functions =
    SOME (collision_transform collision_ctx collision_b) /\
  eval_operands [] collision_packed_call_b = SOME []
Proof
  EVAL_TAC
QED

Theorem collision_packed_b_invoke:
  !fuel.
  step_inst (SUC fuel) collision_output_ctx (mk_inst 4 INVOKE [Label "b"] [])
    collision_packed_call_b = OK (collision_packed_load with vs_inst_idx := 3)
Proof
  gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_b_call_facts,
    collision_packed_b_setup, collision_packed_b_run,
    SRULE [] collision_packed_b_return_merge]
QED

Definition collision_raw_branch_def:
  collision_raw_branch = collision_raw_load with
    <| vs_vars := FEMPTY |+ ("p",(0w:256 word)) |+ ("x",0w); vs_inst_idx := 5 |>
End

Definition collision_packed_branch_def:
  collision_packed_branch = collision_packed_load with
    <| vs_vars := FEMPTY |+ ("p",(32w:256 word)) |+ ("x",1w); vs_inst_idx := 5 |>
End

Theorem collision_zero_byte[local]:
  !a be. set_byte a (0w:8 word) (0w:256 word) be = 0w
Proof
  simp[byteTheory.set_byte_def, byteTheory.word_slice_alt_zero,
    byteTheory.byte_index_def]
QED

Theorem collision_last_byte[local]:
  set_byte (31w:256 word) (1w:8 word) (0w:256 word) T = 1w
Proof
  simp[byteTheory.set_byte_def, byteTheory.byte_index_def,
    byteTheory.word_slice_alt_zero] >>
  rewrite_tac[byteTheory.word_slice_alt_def] >> CONV_TAC WORD_EVAL_CONV
QED

Theorem collision_keep_low_byte[local]:
  !k n. w2n (k:256 word) < 31 /\ n < 8 ==>
    set_byte k (0w:8 word) (n2w (2 ** n):256 word) T = n2w (2 ** n)
Proof
  rpt strip_tac >>
  simp[byteTheory.set_byte_def, byteTheory.byte_index_def,
       byteTheory.word_slice_alt_zero] >>
  rw_tac (std_ss ++ fcpLib.FCP_ss)
    [byteTheory.word_slice_alt_def, wordsTheory.WORD_EQ,
     wordsTheory.word_or_def, wordsTheory.word_index, bitTheory.BIT_TWO_POW] >> decide_tac
QED

Theorem collision_loads_diverge:
  step_inst_base (mk_inst 5 MLOAD [Var "p"] ["x"]) collision_raw_load =
    OK (collision_raw_branch with vs_inst_idx := 4) /\
  step_inst_base (mk_inst 5 MLOAD [Var "p"] ["x"]) collision_packed_load =
    OK (collision_packed_branch with vs_inst_idx := 4)
Proof
  EVAL_TAC >> simp[collision_zero_byte, collision_last_byte,
    SRULE [] (Q.SPECL [`k`,`0`] collision_keep_low_byte)]
QED

Theorem collision_branch_steps:
  step_inst_base (mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] [])
    collision_raw_branch = OK (jump_to "exit" collision_raw_branch) /\
  step_inst_base (mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] [])
    collision_packed_branch = OK (jump_to "bad" collision_packed_branch)
Proof
  EVAL_TAC
QED

Definition collision_main_bb_def:
  collision_main_bb = HD collision_main.fn_blocks
End

Definition collision_output_main_def:
  collision_output_main = collision_transform collision_finished_ctx collision_main
End

Definition collision_output_main_bb_def:
  collision_output_main_bb = HD collision_output_main.fn_blocks
End

Definition collision_bad_entry_def:
  collision_bad_entry = jump_to "bad" collision_packed_branch
End

Definition collision_exit_entry_def:
  collision_exit_entry = jump_to "exit" collision_raw_branch
End

Theorem collision_main_blocks:
  collision_main_bb.bb_instructions =
    [mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"];
     mk_inst 2 MSTORE [Var "p"; Lit 0w] [];
     mk_inst 3 INVOKE [Label "a"] [];
     mk_inst 4 INVOKE [Label "b"] [];
     mk_inst 5 MLOAD [Var "p"] ["x"];
     mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] []] /\
  collision_output_main_bb.bb_instructions =
    [mk_inst 1 ASSIGN [Lit (32w:256 word)] ["p"];
     mk_inst 2 MSTORE [Var "p"; Lit 0w] [];
     mk_inst 3 INVOKE [Label "a"] [];
     mk_inst 4 INVOKE [Label "b"] [];
     mk_inst 5 MLOAD [Var "p"] ["x"];
     mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] []]
Proof
  EVAL_TAC
QED

Theorem collision_main_indices[local]:
  collision_start.vs_inst_idx = 0 /\
  collision_raw_allocated.vs_inst_idx = 0 /\
  collision_packed_allocated.vs_inst_idx = 0 /\
  collision_raw_call_a.vs_inst_idx = 2 /\
  collision_packed_call_a.vs_inst_idx = 2 /\
  collision_raw_call_b.vs_inst_idx = 3 /\
  collision_packed_call_b.vs_inst_idx = 3 /\
  collision_raw_load.vs_inst_idx = 4 /\
  collision_packed_load.vs_inst_idx = 4 /\
  collision_raw_branch.vs_inst_idx = 5 /\
  collision_packed_branch.vs_inst_idx = 5 /\
  ~collision_exit_entry.vs_halted /\ ~collision_bad_entry.vs_halted
Proof
  EVAL_TAC
QED

Theorem collision_main_step_lift[local]:
  !fuel ctx.
  step_inst fuel ctx (mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"])
    collision_start = OK collision_raw_allocated /\
  step_inst fuel ctx (mk_inst 1 ASSIGN [Lit (32w:256 word)] ["p"])
    collision_start = OK collision_packed_allocated /\
  step_inst fuel ctx (mk_inst 2 MSTORE [Var "p"; Lit (0w:256 word)] [])
    (collision_raw_allocated with vs_inst_idx := 1) =
      OK (collision_raw_call_a with vs_inst_idx := 1) /\
  step_inst fuel ctx (mk_inst 2 MSTORE [Var "p"; Lit (0w:256 word)] [])
    (collision_packed_allocated with vs_inst_idx := 1) =
      OK (collision_packed_call_a with vs_inst_idx := 1) /\
  step_inst fuel ctx (mk_inst 5 MLOAD [Var "p"] ["x"]) collision_raw_load =
    OK (collision_raw_branch with vs_inst_idx := 4) /\
  step_inst fuel ctx (mk_inst 5 MLOAD [Var "p"] ["x"]) collision_packed_load =
    OK (collision_packed_branch with vs_inst_idx := 4) /\
  step_inst fuel ctx (mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] [])
    collision_raw_branch = OK collision_exit_entry /\
  step_inst fuel ctx (mk_inst 6 JNZ [Var "x"; Label "bad"; Label "exit"] [])
    collision_packed_branch = OK collision_bad_entry
Proof
  rpt gen_tac >> once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_initial_allocations,
    SRULE [venomInstTheory.mk_inst_def] collision_initial_stores,
    SRULE [venomInstTheory.mk_inst_def] collision_loads_diverge,
    SRULE [venomInstTheory.mk_inst_def] collision_branch_steps,
    collision_exit_entry_def, collision_bad_entry_def]
QED

Theorem collision_main_updates[local]:
  (collision_raw_call_a with vs_inst_idx := 2) = collision_raw_call_a /\
  (collision_packed_call_a with vs_inst_idx := 2) = collision_packed_call_a /\
  (collision_raw_call_b with vs_inst_idx := 3) = collision_raw_call_b /\
  (collision_packed_call_b with vs_inst_idx := 3) = collision_packed_call_b /\
  (collision_raw_load with vs_inst_idx := 4) = collision_raw_load /\
  (collision_packed_load with vs_inst_idx := 4) = collision_packed_load /\
  (collision_raw_branch with vs_inst_idx := 5) = collision_raw_branch /\
  (collision_packed_branch with vs_inst_idx := 5) = collision_packed_branch
Proof
  EVAL_TAC
QED

Theorem collision_raw_main_block:
  !fuel.
  exec_block (SUC fuel) collision_ctx collision_main_bb collision_start =
    OK collision_exit_entry
Proof
  gen_tac >>
  ntac 6 (simp[Once exec_block_def, venomInstTheory.get_instruction_def,
    collision_main_blocks, collision_main_indices, collision_main_updates,
    SRULE [venomInstTheory.mk_inst_def] collision_main_step_lift,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_a_invoke,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_b_invoke,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def])
QED

Theorem collision_packed_main_block:
  !fuel.
  exec_block (SUC fuel) collision_output_ctx collision_output_main_bb collision_start =
    OK collision_bad_entry
Proof
  gen_tac >>
  ntac 6 (simp[Once exec_block_def, venomInstTheory.get_instruction_def,
    collision_main_blocks, collision_main_indices, collision_main_updates,
    SRULE [venomInstTheory.mk_inst_def] collision_main_step_lift,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_a_invoke,
    SRULE [venomInstTheory.mk_inst_def] collision_packed_b_invoke,
    venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def])
QED

Theorem collision_main_entry_facts[local]:
  lookup_block collision_start.vs_current_bb collision_main.fn_blocks =
    SOME collision_main_bb /\
  lookup_block collision_start.vs_current_bb collision_output_main.fn_blocks =
    SOME collision_output_main_bb /\
  eval_phis collision_start collision_main_bb.bb_instructions = OK collision_start /\
  eval_phis collision_start collision_output_main_bb.bb_instructions = OK collision_start /\
  phi_prefix_length collision_main_bb.bb_instructions = 0 /\
  phi_prefix_length collision_output_main_bb.bb_instructions = 0 /\
  (collision_start with vs_inst_idx := 0) = collision_start
Proof
  rpt conj_tac >> EVAL_TAC
QED

Theorem collision_main_continuations:
  !fuel.
  run_blocks (SUC (SUC fuel)) collision_ctx collision_main collision_start =
    run_blocks (SUC fuel) collision_ctx collision_main collision_exit_entry /\
  run_blocks (SUC (SUC fuel)) collision_output_ctx collision_output_main collision_start =
    run_blocks (SUC fuel) collision_output_ctx collision_output_main collision_bad_entry
Proof
  gen_tac >> conj_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_blocks_def])) >>
  simp[collision_main_entry_facts, collision_raw_main_block,
    collision_packed_main_block, collision_main_indices]
QED

Theorem collision_bad_read_checkpoint:
  collision_bad_entry.vs_current_bb = "bad" /\
  collision_bad_entry.vs_inst_idx = 0 /\
  collision_bad_entry.vs_allocas = FEMPTY /\
  lookup_block "bad" collision_output_main.fn_blocks =
    SOME <| bb_label := "bad"; bb_instructions :=
      [mk_inst 7 MLOAD [Lit (1024w:256 word)] ["bad_x"];
       mk_inst 8 STOP [] []] |> /\
  eval_phis collision_bad_entry
    [mk_inst 7 MLOAD [Lit (1024w:256 word)] ["bad_x"];
     mk_inst 8 STOP [] []] = OK collision_bad_entry
Proof
  EVAL_TAC
QED

Theorem collision_raw_exit_facts[local]:
  lookup_block collision_exit_entry.vs_current_bb collision_main.fn_blocks =
    SOME <| bb_label := "exit"; bb_instructions := [mk_inst 9 STOP [] []] |> /\
  eval_phis collision_exit_entry [mk_inst 9 STOP [] []] = OK collision_exit_entry /\
  (collision_exit_entry with vs_inst_idx := 0) = collision_exit_entry /\
  collision_exit_entry.vs_inst_idx = 0 /\
  step_inst_base (mk_inst 9 STOP [] []) collision_exit_entry =
    Halt (collision_exit_entry with vs_halted := T)
Proof
  EVAL_TAC
QED

Theorem collision_raw_exit:
  !fuel ctx.
  run_blocks (SUC fuel) ctx collision_main collision_exit_entry =
    Halt (collision_exit_entry with vs_halted := T)
Proof
  rpt gen_tac >> once_rewrite_tac[run_blocks_def] >>
  simp[collision_raw_exit_facts, phi_prefix_length_def,
    venomInstTheory.mk_inst_def] >>
  once_rewrite_tac[exec_block_def] >>
  simp[venomInstTheory.get_instruction_def, collision_raw_exit_facts] >>
  once_rewrite_tac[step_inst_def] >>
  simp[venomInstTheory.mk_inst_def,
    SRULE [venomInstTheory.mk_inst_def] collision_raw_exit_facts]
QED

Theorem collision_raw_main_run:
  !fuel.
  run_blocks (SUC (SUC fuel)) collision_ctx collision_main collision_start =
    Halt (collision_exit_entry with vs_halted := T)
Proof
  simp[collision_main_continuations, collision_raw_exit]
QED

Theorem collision_stage_leaf_mismatch:
  collision_transform collision_ctx collision_a <> collision_scheduled collision_a /\
  collision_transform collision_ctx collision_b <> collision_scheduled collision_b
Proof
  EVAL_TAC
QED

Theorem collision_input_syntax:
  o1_run_state_ok collision_start /\
  EVERY (\fn. fn.fn_eom = NONE) collision_ctx.ctx_functions /\
  fixed_region_reserved 0 collision_ctx /\
  EVERY ssa_form collision_ctx.ctx_functions /\
  ~ctx_has_dalloca collision_ctx
Proof
  EVAL_TAC >> simp[]
QED

Theorem collision_output_bound:
  ctx_eom_bounded 64 collision_output_ctx
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Theorem collision_shape_check:
  EVERY fn_shape_check collision_ctx.ctx_functions
Proof
  EVAL_TAC
QED

Theorem collision_shapes:
  EVERY fn_shape_ok collision_ctx.ctx_functions
Proof
  mp_tac collision_shape_check >>
  simp[listTheory.EVERY_MEM] >> metis_tac[fn_shape_check_sound]
QED

Theorem collision_context_shape:
  o1_ctx_shape collision_ctx
Proof
  mp_tac (SRULE [collision_ctx_def, venomInstTheory.mk_venom_context_def] collision_shapes) >> strip_tac >>
  simp[o1_ctx_shape_def, collision_ctx_def, venomInstTheory.mk_venom_context_def,
    o1_fn_shape_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

Definition collision_stage_unit_def:
  collision_stage_unit fn =
    <| cu_context := if fn = collision_main then collision_finished_ctx else collision_ctx;
       cu_data_segment := [] |>
End

Definition collision_stage_out_def:
  collision_stage_out fn =
    <| fpo_function := collision_transform (collision_stage_unit fn).cu_context fn;
       fpo_label_map := []; fpo_supply := init_ir_supply (collision_stage_unit fn) |>
End

Theorem collision_stage_units:
  collision_stage_unit collision_a =
    <| cu_context := collision_ctx; cu_data_segment := [] |> /\
  collision_stage_unit collision_b =
    <| cu_context := collision_ctx; cu_data_segment := [] |> /\
  collision_stage_unit collision_main =
    <| cu_context := collision_finished_ctx; cu_data_segment := [] |>
Proof
  `collision_a <> collision_main /\ collision_b <> collision_main` by EVAL_TAC >>
  simp[collision_stage_unit_def]
QED

Theorem collision_option_result[local]:
  OPTION_MAP f x = SOME y ==> x = SOME (THE x)
Proof
  Cases_on `x` >> simp[]
QED

Theorem collision_concretize_results:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    concretize_function_fuel_in_context (concretize_memloc_fuel fn)
      (collision_stage_unit fn).cu_context [] fn =
    SOME (collision_transform (collision_stage_unit fn).cu_context fn)
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[collision_stage_units, collision_transform_def] >>
  metis_tac[collision_option_result, collision_leaf_layouts, collision_finished_layout]
QED

Theorem collision_stage_reserved:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    (collision_stage_unit fn).cu_context.ctx_global_reserved = []
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[collision_stage_units, collision_ctx_def, collision_finished_ctx_def,
    venomInstTheory.mk_venom_context_def]
QED

Theorem collision_stage_execute:
  !fn s. MEM fn [collision_a; collision_b; collision_main] ==>
    execute_configured_fn_pass ARB (CFP_Simple VP_ConcretizeMemLoc)
      (collision_stage_unit fn) s fn =
    SOME ((collision_stage_out fn) with fpo_supply := s)
Proof
  rpt strip_tac >> drule collision_concretize_results >> strip_tac >>
  drule collision_stage_reserved >> strip_tac >>
  simp[execute_configured_fn_pass_def, collision_stage_out_def]
QED

Theorem collision_output_main_exact:
  collision_output_main = collision_main with
    <| fn_blocks :=
         (HD collision_main.fn_blocks with bb_instructions :=
            mk_inst 1 ASSIGN [Lit (32w:256 word)] ["p"] ::
            TL (HD collision_main.fn_blocks).bb_instructions) ::
         TL collision_main.fn_blocks;
       fn_eom := SOME 64;
       fn_mems_used := [(Allocation 1,32,32); (Allocation 100,0,32)] |>
Proof
  EVAL_TAC
QED

Theorem collision_stage_effects:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    (collision_stage_out fn).fpo_function.fn_name = fn.fn_name /\
    fn_pass_effects_hold VP_ConcretizeMemLoc fn (collision_stage_out fn) /\
    introduces_no_invoke_edges fn (collision_stage_out fn).fpo_function
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[collision_stage_out_def, collision_stage_units,
    GSYM collision_output_main_def, collision_output_main_exact,
    collision_a_exact, collision_b_exact] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem collision_stage_lookups:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    lookup_unique_function fn.fn_name
      (collision_stage_unit fn).cu_context.ctx_functions = SOME fn
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[collision_stage_units, collision_ctx_def, collision_finished_ctx_def,
    venomInstTheory.mk_venom_context_def, lookup_unique_function_def,
    collision_scheduled_def, collision_expanded_def, collision_sealed_def,
    collision_a_exact, collision_b_exact,
    collision_a_def, collision_b_def, collision_main_def,
    venomInstTheory.mk_raw_function_def]
QED

Theorem collision_stage_supplies:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    ir_supply_covers_unit (init_ir_supply (collision_stage_unit fn))
      (collision_stage_unit fn) /\
    ir_supply_extends (init_ir_supply (collision_stage_unit fn))
      (collision_stage_out fn).fpo_supply /\
    ir_supply_covers_fn (collision_stage_out fn).fpo_supply
      (collision_stage_out fn).fpo_function /\
    ir_supply_covers_unit (collision_stage_out fn).fpo_supply
      (collision_stage_unit fn)
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[collision_stage_out_def, collision_stage_units,
    GSYM collision_output_main_def, collision_output_main_exact,
    collision_a_exact, collision_b_exact] >>
  rewrite_tac[collision_finished_ctx_def, collision_scheduled_def,
    collision_expanded_def, collision_sealed_def, collision_a_exact,
    collision_b_exact] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem collision_stage_steps:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    fn_pass_step ARB (CFP_Simple VP_ConcretizeMemLoc)
      (collision_stage_unit fn) (init_ir_supply (collision_stage_unit fn))
      fn (collision_stage_out fn)
Proof
  rpt strip_tac >>
  drule collision_stage_lookups >> strip_tac >>
  drule collision_stage_effects >> strip_tac >>
  drule collision_stage_supplies >> strip_tac >>
  drule collision_stage_execute >>
  disch_then (qspec_then `init_ir_supply (collision_stage_unit fn)` assume_tac) >>
  gvs[fn_pass_step_def, venomPassScheduleTheory.fn_pass_tag_def, collision_stage_out_def]
QED

Theorem collision_fmp_step:
  !fn. MEM fn [collision_a; collision_b] ==>
    fn_pass_step ARB (CFP_Simple VP_FmpLowering)
      collision_unit (init_ir_supply collision_unit)
      (collision_transform collision_ctx fn)
      <| fpo_function := collision_sealed fn;
         fpo_label_map := []; fpo_supply := init_ir_supply collision_unit |>
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[fn_pass_step_def, collision_fmp_exact,
    venomPassScheduleTheory.fn_pass_tag_def] >>
  rewrite_tac[collision_unit_def, collision_observed_def, collision_sealed_def,
    collision_a_exact, collision_b_exact] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem collision_sealed_steps:
  !fn pass. MEM fn [collision_a; collision_b] /\
    MEM pass [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG] ==>
    fn_pass_step ARB pass (collision_current_unit (collision_sealed fn))
      (init_ir_supply collision_unit) (collision_sealed fn)
      <| fpo_function := collision_sealed fn;
         fpo_label_map := []; fpo_supply := init_ir_supply collision_unit |>
Proof
  rpt gen_tac >> pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[fn_pass_step_def, collision_ssa_exact, collision_simplify_exact,
    venomPassScheduleTheory.fn_pass_tag_def] >>
  rewrite_tac[collision_current_unit_def, collision_unit_def,
    collision_observed_def, collision_sealed_def, collision_a_exact,
    collision_b_exact] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem collision_layout_steps:
  !fn. MEM fn [collision_a; collision_b] ==>
    fn_pass_step ARB (CFP_Simple VP_SingleUseExpansion)
      (collision_current_unit (collision_sealed fn))
      (init_ir_supply collision_unit) (collision_sealed fn)
      <| fpo_function := collision_expanded fn; fpo_label_map := [];
         fpo_supply := collision_expanded_supply fn |> /\
    fn_pass_step ARB (CFP_Simple VP_DFT)
      (collision_current_unit (collision_expanded fn))
      (collision_expanded_supply fn) (collision_expanded fn)
      <| fpo_function := collision_scheduled fn; fpo_label_map := [];
         fpo_supply := collision_expanded_supply fn |> /\
    fn_pass_step ARB (CFP_Simple VP_CFGNormalization)
      (collision_current_unit (collision_scheduled fn))
      (collision_expanded_supply fn) (collision_scheduled fn)
      <| fpo_function := collision_scheduled fn; fpo_label_map := [];
         fpo_supply := collision_expanded_supply fn |>
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[fn_pass_step_def, collision_expansion_exact, collision_dft_exact,
    collision_normalization_exact, venomPassScheduleTheory.fn_pass_tag_def] >>
  rewrite_tac[collision_expanded_supply_def, collision_scheduled_def,
    collision_expanded_def, collision_current_unit_def, collision_unit_def,
    collision_observed_def, collision_sealed_def, collision_a_exact,
    collision_b_exact] >>
  rpt conj_tac >> EVAL_TAC
QED

Theorem collision_leaf_later:
  !fn. MEM fn [collision_a; collision_b] ==>
    fn_steps ARB (DROP 3 venomPassSchedule$o1_fn_passes)
      (collision_transform collision_ctx fn) (collision_scheduled fn)
Proof
  rpt strip_tac >>
  drule collision_fmp_step >> strip_tac >>
  drule collision_sealed_steps >> strip_tac >>
  drule collision_layout_steps >> strip_tac >>
  simp[venomPassScheduleTheory.o1_fn_passes_def] >>
  ntac 6 (simp[Once fn_steps_def] >> first_assum (irule_at Any) >> simp[]) >>
  simp[fn_steps_def]
QED

Theorem collision_calls:
  fn_invoke_targets collision_a = [] /\
  fn_invoke_targets collision_b = [] /\
  fn_invoke_targets collision_main = ["a"; "b"]
Proof
  EVAL_TAC
QED

Theorem collision_leaf_names:
  (collision_transform collision_ctx collision_a).fn_name = "a" /\
  (collision_transform collision_ctx collision_b).fn_name = "b" /\
  (collision_scheduled collision_a).fn_name = "a" /\
  (collision_scheduled collision_b).fn_name = "b"
Proof
  simp[collision_scheduled_def, collision_expanded_def, collision_sealed_def,
    collision_a_exact, collision_b_exact, collision_a_def, collision_b_def,
    venomInstTheory.mk_raw_function_def]
QED

Theorem collision_callee_lookups:
  lookup_function "a" collision_output_ctx.ctx_functions =
    SOME (collision_transform collision_ctx collision_a) /\
  lookup_function "b" collision_output_ctx.ctx_functions =
    SOME (collision_transform collision_ctx collision_b) /\
  lookup_function "a" collision_finished_ctx.ctx_functions =
    SOME (collision_scheduled collision_a) /\
  lookup_function "b" collision_finished_ctx.ctx_functions =
    SOME (collision_scheduled collision_b)
Proof
  simp[collision_output_ctx_def, collision_finished_ctx_def,
    venomInstTheory.mk_venom_context_def, venomInstTheory.lookup_function_def,
    listTheory.FIND_thm, collision_leaf_names]
QED

Theorem collision_walk_views:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    o1_walk_view ARB 2 collision_output_ctx fn (collision_stage_unit fn)
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[o1_walk_view_def, walk_view_def, collision_stage_units,
    collision_calls, collision_callee_lookups] >>
  rpt strip_tac >> gvs[collision_callee_lookups] >>
  simp[collision_leaf_later]
QED

Theorem collision_stage_headers:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    (collision_stage_unit fn).cu_context.ctx_entry = collision_ctx.ctx_entry /\
    (collision_stage_unit fn).cu_context.ctx_global_reserved =
      collision_ctx.ctx_global_reserved /\
    ctx_fn_names (collision_stage_unit fn).cu_context = ctx_fn_names collision_ctx
Proof
  pure_rewrite_tac[listTheory.MEM] >> rpt strip_tac >> gvs[] >>
  simp[collision_stage_units, collision_ctx_def, collision_finished_ctx_def,
    venomInstTheory.mk_venom_context_def, venomInstTheory.ctx_fn_names_def,
    collision_leaf_names] >> EVAL_TAC
QED

Theorem collision_stage_list:
  !fn. MEM fn [collision_a; collision_b; collision_main] ==>
    ?observed s out.
      fn_pass_step ARB (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
      out.fpo_function = (collision_stage_out fn).fpo_function /\
      observed.cu_context.ctx_entry = collision_ctx.ctx_entry /\
      observed.cu_context.ctx_global_reserved = collision_ctx.ctx_global_reserved /\
      ctx_fn_names observed.cu_context = ctx_fn_names collision_ctx /\
      o1_walk_view ARB 2 collision_output_ctx fn observed
Proof
  rpt strip_tac >>
  qexistsl_tac [`collision_stage_unit fn`, `init_ir_supply (collision_stage_unit fn)`,
    `collision_stage_out fn`] >>
  simp[collision_stage_steps, collision_stage_headers, collision_walk_views]
QED

Theorem collision_stage_context_fields:
  collision_output_ctx.ctx_entry = collision_ctx.ctx_entry /\
  collision_output_ctx.ctx_global_reserved = collision_ctx.ctx_global_reserved /\
  collision_ctx.ctx_functions = [collision_a; collision_b; collision_main] /\
  collision_output_ctx.ctx_functions =
    [(collision_stage_out collision_a).fpo_function;
     (collision_stage_out collision_b).fpo_function;
     (collision_stage_out collision_main).fpo_function]
Proof
  simp[collision_output_ctx_def, collision_finished_ctx_def, collision_ctx_def,
    venomInstTheory.mk_venom_context_def, collision_stage_out_def,
    collision_stage_units]
QED

Theorem collision_actual_stage:
  ctx_pass_stage ARB (CFP_Simple VP_ConcretizeMemLoc) (o1_walk_view ARB 2)
    collision_ctx collision_output_ctx
Proof
  simp[ctx_pass_stage_def, collision_stage_context_fields] >>
  rpt conj_tac >> irule collision_stage_list >> simp[]
QED
