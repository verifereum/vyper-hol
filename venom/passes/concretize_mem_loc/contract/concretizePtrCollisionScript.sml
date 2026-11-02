(* Production-layout probe for cross-function allocation identity collisions. *)
Theory concretizePtrCollision
Ancestors concretizeMemLocDefs venomPassDispatcher venomExecSemantics
  venomFnScheduleRunner
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
    [collision_scheduled collision_a; collision_scheduled collision_b;
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
