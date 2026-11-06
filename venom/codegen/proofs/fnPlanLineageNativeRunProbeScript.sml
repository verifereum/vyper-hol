Theory fnPlanLineageNativeRunProbe
Ancestors
  fnPlanLineageEntryProduction codegenReadyCompute stackPlanGen livenessDefs
Libs wordsLib

(* Native residual repetition, not PHI-class aliasing. *)
Definition native_duplicate_fn_def:
  native_duplicate_fn = mk_raw_function "native_duplicate"
    [<| bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["x"];
         mk_inst 1 PARAM [Lit 1w] ["c"];
         mk_inst 2 JNZ [Var "c"; Label "L"; Label "R"] []] |>;
     <| bb_label := "L"; bb_instructions :=
        [mk_inst 3 JMP [Label "J"] []] |>;
     <| bb_label := "R"; bb_instructions :=
        [mk_inst 4 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [mk_inst 5 ADD [Var "x"; Var "x"] ["y"];
         mk_inst 6 MSTORE [Lit 0w; Var "y"] [];
         mk_inst 7 STOP [] []] |>]
End

Theorem native_duplicate_ready:
  codegen_ready_fn native_duplicate_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem native_duplicate_marker_free:
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) native_duplicate_fn.fn_blocks
Proof
  EVAL_TAC
QED

Theorem native_duplicate_targets:
  join_target_ops (liveness_analyze native_duplicate_fn) native_duplicate_fn
    "L" (mk_inst 3 JMP [Label "J"] []) = SOME [Var "x"; Var "x"]
Proof
  EVAL_TAC
QED

Definition native_duplicate_entry_def:
  native_duplicate_entry = SND (THE (generate_block_plan
    (liveness_analyze native_duplicate_fn) (dfg_build_function native_duplicate_fn)
    (cfg_analyze native_duplicate_fn) native_duplicate_fn
    (THE (lookup_block "E" native_duplicate_fn.fn_blocks))
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem native_duplicate_entry_stack:
  native_duplicate_entry.ps_stack = [Var "x"] /\
  native_duplicate_entry.ps_spilled = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

Theorem native_duplicate_entry_exact:
  native_duplicate_entry =
    (init_cleanup_plan_state NONE [] 0 0) with ps_stack := [Var "x"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem native_duplicate_left_none:
  generate_block_plan (liveness_analyze native_duplicate_fn)
    (dfg_build_function native_duplicate_fn) (cfg_analyze native_duplicate_fn)
    native_duplicate_fn (THE (lookup_block "L" native_duplicate_fn.fn_blocks))
    native_duplicate_entry = NONE
Proof
  rewrite_tac[native_duplicate_entry_exact] >> EVAL_TAC >> simp[]
QED

Definition native_padded_names_def:
  native_padded_names =
    ["p00";"p01";"p02";"p03";"p04";"p05";"p06";"p07";
     "p08";"p09";"p10";"p11";"p12";"p13";"p14";"p15"]
End

Definition native_padded_fn_def:
  native_padded_fn = mk_raw_function "native_padded"
    [<| bb_label := "E"; bb_instructions :=
        MAPi (\i v. mk_inst i PARAM [Lit (n2w i)] [v])
          (["x"; "c"] ++ native_padded_names) ++
        [mk_inst 18 JNZ [Var "c"; Label "L"; Label "R"] []] |>;
     <| bb_label := "L"; bb_instructions :=
        [mk_inst 19 JMP [Label "J"] []] |>;
     <| bb_label := "R"; bb_instructions :=
        [mk_inst 20 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        [mk_inst 21 ADD [Var "x"; Var "x"] ["y"];
         mk_inst 22 MSTORE [Lit 0w; Var "y"] []] ++
        MAPi (\i v. mk_inst (23+i) MSTORE [Lit (n2w (i+1)); Var v] [])
          native_padded_names ++
        [mk_inst 39 STOP [] []] |>]
End

Theorem native_padded_ready:
  codegen_ready_fn native_padded_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem native_padded_marker_free:
  EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb.bb_instructions) native_padded_fn.fn_blocks
Proof
  EVAL_TAC
QED

Theorem native_padded_targets:
  join_target_ops (liveness_analyze native_padded_fn) native_padded_fn
    "L" (mk_inst 19 JMP [Label "J"] []) =
    SOME (REVERSE (MAP Var native_padded_names) ++ [Var "x"; Var "x"])
Proof
  EVAL_TAC
QED

Definition native_padded_entry_def:
  native_padded_entry = SND (THE (generate_block_plan
    (liveness_analyze native_padded_fn) (dfg_build_function native_padded_fn)
    (cfg_analyze native_padded_fn) native_padded_fn
    (THE (lookup_block "E" native_padded_fn.fn_blocks))
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem native_padded_entry_stack:
  native_padded_entry =
    (init_cleanup_plan_state NONE [] 0 0) with ps_stack :=
      [Var "x"; Var "p15"; Var "p00"; Var "p01"; Var "p02"; Var "p03";
       Var "p04"; Var "p05"; Var "p06"; Var "p07"; Var "p08"; Var "p09";
       Var "p10"; Var "p11"; Var "p12"; Var "p13"; Var "p14"]
Proof
  EVAL_TAC >> simp[]
QED

Theorem native_padded_left_none:
  generate_block_plan (liveness_analyze native_padded_fn)
    (dfg_build_function native_padded_fn) (cfg_analyze native_padded_fn)
    native_padded_fn (THE (lookup_block "L" native_padded_fn.fn_blocks))
    native_padded_entry = NONE
Proof
  rewrite_tac[native_padded_entry_stack] >> EVAL_TAC >> simp[]
QED

Theorem native_duplicate_entry_some:
  IS_SOME (generate_block_plan (liveness_analyze native_duplicate_fn)
    (dfg_build_function native_duplicate_fn) (cfg_analyze native_duplicate_fn)
    native_duplicate_fn (THE (lookup_block "E" native_duplicate_fn.fn_blocks))
    (init_cleanup_plan_state NONE [] 0 0))
Proof
  EVAL_TAC >> simp[]
QED

Theorem native_padded_entry_some:
  IS_SOME (generate_block_plan (liveness_analyze native_padded_fn)
    (dfg_build_function native_padded_fn) (cfg_analyze native_padded_fn)
    native_padded_fn (THE (lookup_block "E" native_padded_fn.fn_blocks))
    (init_cleanup_plan_state NONE [] 0 0))
Proof
  EVAL_TAC >> simp[]
QED

(* The actual initialized entry succeeds at both sizes.  Its saved physical
   state has one x and no spilled x; the native target demands two x entries.
   The next L block is rejected, so neither fixture witnesses a successful
   function plan or falsifies the frozen theorem.  In particular these two
   rejections are not a universal successful-run multiplicity producer. *)
