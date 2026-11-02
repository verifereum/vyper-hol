(* Production-layout probe for cross-function allocation identity collisions. *)
Theory concretizePtrCollision
Ancestors concretizeMemLocDefs venomPassDispatcher venomExecSemantics
  venomFnScheduleRunner
Libs wordsLib

Definition collision_a_def:
  collision_a = mk_raw_function "a"
    [<| bb_label := "a"; bb_instructions :=
      [mk_inst 100 ALLOCA [Lit (32w:256 word)] ["a_p"];
       mk_inst 101 MSTORE [Var "a_p"; Lit 0w] [];
       mk_inst 102 RET [] []] |>]
End

Definition collision_b_def:
  collision_b = mk_raw_function "b"
    [<| bb_label := "b"; bb_instructions :=
      [mk_inst 100 ALLOCA [Lit (64w:256 word)] ["b_p"];
       mk_inst 103 ADD [Var "b_p"; Lit 32w] ["b_q"];
       mk_inst 104 MSTORE [Var "b_q"; Lit 1w] [];
       mk_inst 105 RET [] []] |>]
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
        [mk_inst 100 ASSIGN [Lit (0w:256 word)] ["a_p"];
         mk_inst 101 MSTORE [Var "a_p"; Lit 0w] [];
         mk_inst 102 RET [] []] |>]) with
      <| fn_eom := SOME 32; fn_mems_used := [(Allocation 100,0,32)] |>
Proof
  EVAL_TAC
QED

Theorem collision_b_exact:
  collision_transform collision_ctx collision_b =
    (mk_raw_function "b"
      [<| bb_label := "b"; bb_instructions :=
        [mk_inst 100 ASSIGN [Lit (0w:256 word)] ["b_p"];
         mk_inst 103 ADD [Var "b_p"; Lit 32w] ["b_q"];
         mk_inst 104 MSTORE [Var "b_q"; Lit 1w] [];
         mk_inst 105 RET [] []] |>]) with
      <| fn_eom := SOME 64; fn_mems_used := [(Allocation 100,0,64)] |>
Proof
  EVAL_TAC
QED

Theorem collision_fmp_a_rejected:
  execute_configured_fn_pass ARB (CFP_Simple VP_FmpLowering)
    collision_unit (init_ir_supply collision_unit)
    (collision_transform collision_ctx collision_a) = NONE
Proof
  rewrite_tac[collision_unit_def, collision_observed_def,
    collision_a_exact, collision_b_exact] >> EVAL_TAC >> simp[finite_mapTheory.FEVERY_DEF]
QED
