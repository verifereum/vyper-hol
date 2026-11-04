(* Checked production-layout probes: post-call overwrite and fuel sensitivity. *)
Theory concretizePtrLayoutProbe
Ancestors
  concretizeMemLocDefs calleeMemoryWitness words
Libs wordsLib

Definition ptr_probe_ctx_def:
  ptr_probe_ctx = mk_venom_context
    [(mk_raw_function "leaf" []) with
       fn_mems_used := [(Allocation 100,0,32)]] (SOME "caller")
End

Definition ptr_probe_fn_def:
  ptr_probe_fn killed = mk_raw_function "caller"
    [<| bb_label := "entry"; bb_instructions :=
      [mk_inst 201 ALLOCA [Lit (32w:256 word)] ["p"];
       mk_inst 202 MSTORE [Var "p"; Lit 1w] [];
       mk_inst 203 INVOKE [Label "leaf"] []] ++
      (if killed then [mk_inst 204 MSTORE [Var "p"; Lit 2w] []] else []) ++
      [mk_inst 205 MLOAD [Var "p"] ["x"];
       mk_inst 206 STOP [] []] |>]
End

Definition ptr_probe_ls_def:
  ptr_probe_ls fuel killed =
    context_mem_livesets fuel ptr_probe_ctx (ptr_probe_fn killed)
      (bp_analyze_fuel fuel (cfg_analyze (ptr_probe_fn killed)) (ptr_probe_fn killed))
      (cfg_analyze (ptr_probe_fn killed))
End

Definition ptr_probe_layout_def:
  ptr_probe_layout fuel killed =
    OPTION_MAP (\layout. (FLOOKUP layout.cl_positions (Allocation 201),layout.cl_eom))
      (compute_function_layout_fuel_in_context fuel ptr_probe_ctx [] (ptr_probe_fn killed))
End

Theorem ptr_probe_protected_ls_20:
  ptr_probe_ls 20 F =
    FEMPTY |+ (Allocation 100,[("entry",2)])
      |+ (Allocation 201,[("entry",1); ("entry",2); ("entry",3)])
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem ptr_probe_protected_layout_20:
  ptr_probe_layout 20 F = SOME (SOME 32,64)
Proof
  EVAL_TAC
QED

Theorem ptr_probe_killed_ls_20:
  ptr_probe_ls 20 T =
    FEMPTY |+ (Allocation 100,[("entry",2)])
      |+ (Allocation 201,[("entry",1); ("entry",3); ("entry",4)])
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem ptr_probe_layout_fuel:
  ptr_probe_layout 0 F = SOME (SOME 32,64) /\
  ptr_probe_layout 1 F = SOME (SOME 32,64) /\
  ptr_probe_layout 0 T = SOME (SOME 32,64) /\
  ptr_probe_layout 1 T = SOME (SOME 0,32) /\
  ptr_probe_layout 20 T = SOME (SOME 0,32)
Proof
  EVAL_TAC
QED

Theorem ptr_probe_ls_low_fuel:
  ptr_probe_ls 0 F = FEMPTY /\
  ptr_probe_ls 0 T = FEMPTY /\
  ptr_probe_ls 1 F = ptr_probe_ls 20 F /\
  ptr_probe_ls 1 T = ptr_probe_ls 20 T
Proof
  EVAL_TAC
QED
