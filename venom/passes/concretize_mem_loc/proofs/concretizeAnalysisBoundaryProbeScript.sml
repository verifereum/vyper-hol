(* Executable finite-analysis boundary probes; no stage claims. *)
Theory concretizeAnalysisBoundaryProbe
Ancestors concretizeMemLocDefs venomExecSemantics
Libs wordsLib

Definition boundary_loop_def:
  boundary_loop = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 1 ALLOCA [Lit (64w:256 word)] ["p"];
        mk_inst 2 ALLOCA [Lit 32w] ["q"];
        mk_inst 3 JMP [Label "loop"] []] |>;
     <| bb_label := "loop"; bb_instructions :=
       [mk_inst 4 PHI [Label "entry"; Var "p"; Label "loop"; Var "next"] ["cur"];
        mk_inst 5 MSTORE [Var "q"; Lit 2w] [];
        mk_inst 6 MLOAD [Var "cur"] ["x"];
        mk_inst 7 ADD [Var "cur"; Lit 1w] ["next"];
        mk_inst 8 JNZ [Lit 0w; Label "loop"; Label "exit"] []] |>;
     <| bb_label := "exit"; bb_instructions :=
       [mk_inst 9 STOP [] []] |>]
End

Definition boundary_bp_def:
  boundary_bp fn = bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn
End

Theorem boundary_loop_order:
  (cfg_analyze boundary_loop).cfg_dfs_pre = ["entry"; "loop"; "exit"]
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Definition boundary_map_def:
  boundary_map off nextoff =
    FEMPTY |+ ("p", [Ptr (Allocation 1) (SOME 0)])
           |+ ("q", [Ptr (Allocation 2) (SOME 0)])
           |+ ("cur", [Ptr (Allocation 1) off])
           |+ ("next", [Ptr (Allocation 1) nextoff])
End

Theorem boundary_loop_pass1:
  bp_one_pass boundary_loop ["entry"; "loop"; "exit"] FEMPTY =
    (T, boundary_map (SOME 0) (SOME 1))
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem boundary_loop_pass2:
  bp_one_pass boundary_loop ["entry"; "loop"; "exit"]
    (boundary_map (SOME 0) (SOME 1)) = (T, boundary_map NONE NONE)
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem boundary_loop_pass3:
  bp_one_pass boundary_loop ["entry"; "loop"; "exit"]
    (boundary_map NONE NONE) = (F, boundary_map NONE NONE)
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem boundary_loop_fuel:
  concretize_memloc_fuel boundary_loop = 52
Proof
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem boundary_loop_bp:
  boundary_bp boundary_loop =
    FEMPTY |+ ("p", [Ptr (Allocation 1) (SOME 0)])
           |+ ("q", [Ptr (Allocation 2) (SOME 0)])
           |+ ("cur", [Ptr (Allocation 1) NONE])
           |+ ("next", [Ptr (Allocation 1) NONE])
Proof
  rewrite_tac[boundary_bp_def, bp_analyze_fuel_def, boundary_loop_order,
              boundary_loop_fuel] >>
  CONV_TAC (LAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV numLib.num_CONV))))) >>
  simp[bp_iterate_fuel_def, boundary_loop_pass1] >>
  CONV_TAC (LAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV numLib.num_CONV))))) >>
  simp[bp_iterate_fuel_def, boundary_loop_pass2] >>
  CONV_TAC (LAND_CONV (RATOR_CONV (RATOR_CONV (RATOR_CONV (RAND_CONV numLib.num_CONV))))) >>
  simp[bp_iterate_fuel_def, boundary_loop_pass3, boundary_map_def]
QED

Theorem boundary_loop_base:
  bp_get_ptrs (boundary_bp boundary_loop) "cur" = [Ptr (Allocation 1) NONE] /\
  bp_get_ptrs (boundary_bp boundary_loop) "next" = [Ptr (Allocation 1) NONE] /\
  bp_one_pass boundary_loop (cfg_analyze boundary_loop).cfg_dfs_pre
    (boundary_bp boundary_loop) = (F, boundary_bp boundary_loop)
Proof
  rewrite_tac[boundary_loop_bp, boundary_loop_order] >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Definition boundary_ctx_def:
  boundary_ctx = mk_venom_context [boundary_loop] (SOME "main")
End

Theorem boundary_loop_liveness_overlap:
  MEM ("loop",1)
    (THE (FLOOKUP (context_mem_livesets (concretize_memloc_fuel boundary_loop)
      boundary_ctx boundary_loop (boundary_bp boundary_loop) (cfg_analyze boundary_loop))
      (Allocation 1))) /\
  MEM ("loop",1)
    (THE (FLOOKUP (context_mem_livesets (concretize_memloc_fuel boundary_loop)
      boundary_ctx boundary_loop (boundary_bp boundary_loop) (cfg_analyze boundary_loop))
      (Allocation 2)))
Proof
  rewrite_tac[boundary_loop_bp, boundary_loop_fuel] >>
  EVAL_TAC
QED

Theorem boundary_loop_layout:
  OPTION_MAP (\fn. MAP (\i. i.inst_operands)
    (HD fn.fn_blocks).bb_instructions)
    (concretize_function_fuel_in_context (concretize_memloc_fuel boundary_loop)
      boundary_ctx [] boundary_loop) =
    SOME [[Lit (32w:256 word)]; [Lit 0w]; [Label "loop"]]
Proof
  rewrite_tac[concretize_function_fuel_in_context_def,
    compute_function_layout_fuel_in_context_def] >>
  rewrite_tac[GSYM boundary_bp_def] >>
  rewrite_tac[boundary_loop_bp, boundary_loop_fuel] >>
  EVAL_TAC
QED

(* The taken path defines x first, although DFS can visit its use first. *)
Definition boundary_late_def:
  boundary_late = mk_raw_function "main"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 1 ALLOCA [Lit (32w:256 word)] ["p"];
        mk_inst 2 ALLOCA [Lit 32w] ["q"];
        mk_inst 3 MSTORE [Var "p"; Lit 1w] [];
        mk_inst 4 JNZ [Lit 1w; Label "def"; Label "use"] []] |>;
     <| bb_label := "use"; bb_instructions :=
       [mk_inst 5 ASSIGN [Var "x"] ["y"];
        mk_inst 6 MSTORE [Var "q"; Lit 2w] [];
        mk_inst 7 MLOAD [Var "y"] ["v"];
        mk_inst 8 STOP [] []] |>;
     <| bb_label := "def"; bb_instructions :=
       [mk_inst 9 ASSIGN [Var "p"] ["x"];
        mk_inst 10 JMP [Label "use"] []] |>]
End

Theorem boundary_late_order:
  (cfg_analyze boundary_late).cfg_dfs_pre = ["entry"; "use"; "def"]
Proof
  EVAL_TAC
QED

Theorem boundary_late_base:
  bp_get_ptrs (boundary_bp boundary_late) "y" =
    [Ptr (Allocation 1) (SOME 0)] /\
  bp_one_pass boundary_late (cfg_analyze boundary_late).cfg_dfs_pre
    (boundary_bp boundary_late) = (F, boundary_bp boundary_late)
Proof
  rewrite_tac[boundary_bp_def, bp_analyze_fuel_def, boundary_late_order] >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ, finite_mapTheory.FUPDATE_COMMUTES]
QED

Theorem boundary_late_bp:
  boundary_bp boundary_late =
    FEMPTY |+ ("p", [Ptr (Allocation 1) (SOME 0)])
           |+ ("q", [Ptr (Allocation 2) (SOME 0)])
           |+ ("x", [Ptr (Allocation 1) (SOME 0)])
           |+ ("y", [Ptr (Allocation 1) (SOME 0)])
Proof
  rewrite_tac[boundary_bp_def, bp_analyze_fuel_def, boundary_late_order] >>
  EVAL_TAC >> simp[finite_mapTheory.fmap_eq_flookup, finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `x = "x"` >> Cases_on `x = "y"` >> gvs[]
QED

Definition boundary_late_ctx_def:
  boundary_late_ctx = mk_venom_context [boundary_late] (SOME "main")
End

Theorem boundary_late_liveness_overlap:
  MEM ("use",1)
    (THE (FLOOKUP (context_mem_livesets (concretize_memloc_fuel boundary_late)
      boundary_late_ctx boundary_late (boundary_bp boundary_late) (cfg_analyze boundary_late))
      (Allocation 1))) /\
  MEM ("use",1)
    (THE (FLOOKUP (context_mem_livesets (concretize_memloc_fuel boundary_late)
      boundary_late_ctx boundary_late (boundary_bp boundary_late) (cfg_analyze boundary_late))
      (Allocation 2)))
Proof
  rewrite_tac[boundary_late_bp] >> EVAL_TAC
QED

Theorem boundary_late_layout:
  OPTION_MAP (\fn. MAP (\i. i.inst_operands)
    (HD fn.fn_blocks).bb_instructions)
    (concretize_function_fuel_in_context (concretize_memloc_fuel boundary_late)
      boundary_late_ctx [] boundary_late) =
    SOME [[Lit (32w:256 word)]; [Lit 0w]; [Var "p"; Lit 1w];
      [Lit 1w; Label "def"; Label "use"]]
Proof
  rewrite_tac[concretize_function_fuel_in_context_def,
    compute_function_layout_fuel_in_context_def] >>
  rewrite_tac[GSYM boundary_bp_def, boundary_late_bp] >>
  EVAL_TAC
QED

(* A syntactic forward reference alone is not semantic counterevidence. *)
Definition boundary_undefined_def:
  boundary_undefined = mk_raw_function "main"
    [<| bb_label := "main"; bb_instructions :=
       [mk_inst 1 ASSIGN [Var "late"] ["early"];
        mk_inst 2 ALLOCA [Lit (32w:256 word)] ["late"];
        mk_inst 3 ALLOCA [Lit 32w] ["q"];
        mk_inst 4 MSTORE [Var "q"; Lit 2w] [];
        mk_inst 5 MLOAD [Var "early"] ["v"];
        mk_inst 6 STOP [] []] |>]
End

Theorem boundary_undefined_rejected:
  run_context 10 (mk_venom_context [boundary_undefined] (SOME "main"))
    (init_venom_state "main") = Error "undefined operand"
Proof
  EVAL_TAC
QED
