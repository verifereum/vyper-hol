Theory fnPlanLineageDeepJoinProbe
Ancestors
  fnPlanLineageResidualProbe fnPlanLineagePhiTemporalProbe
  fnPlanLineageJoinEntry codegenReadyCompute fnPlanLineageStages
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst cfgTransform

Definition deep_join_vars_def:
  deep_join_vars = ["v00";"v01";"v02";"v03";"v04";"v05";"v06";"v07";
    "v08";"v09";"v10";"v11";"v12";"v13";"v14";"v15"]
End

Definition deep_join_fn_def:
  deep_join_fn rev n = mk_raw_function "deep_join"
    [<|bb_label := "E"; bb_instructions :=
       [mk_inst 0 PARAM [Lit 0w] ["c"]] ++
       MAPi (\i v. mk_inst (i+1) PARAM [Lit (n2w (i+1))] [v])
         (TAKE (n-2) deep_join_vars) ++
       [mk_inst 20 JNZ (if rev then [Var "c"; Label "B"; Label "A"]
                        else [Var "c"; Label "A"; Label "B"]) []]|>;
     <|bb_label := "A"; bb_instructions :=
       [mk_inst 21 ADD [Lit 1w; Lit 2w] ["a0"];
        mk_inst 22 ADD [Lit 3w; Lit 4w] ["a1"];
        mk_inst 23 OFFSET [Lit 0w; Label "J"] ["r"];
        mk_inst 24 JMP [Label "J"] []]|>;
     <|bb_label := "B"; bb_instructions :=
       [mk_inst 25 ADD [Lit 5w; Lit 6w] ["b0"];
        mk_inst 26 ADD [Lit 7w; Lit 8w] ["b1"];
        mk_inst 27 JMP [Label "J"] []]|>;
     <|bb_label := "J"; bb_instructions :=
       [mk_inst 28 PHI [Label "A"; Var "a0"; Label "B"; Var "b0"] ["x0"];
        mk_inst 29 PHI [Label "A"; Var "a1"; Label "B"; Var "b1"] ["x1"]] ++
       MAPi (\i v. mk_inst (30+i) MSTORE [Lit (n2w i); Var v] [])
         (["x0"; "x1"] ++ TAKE (n-2) deep_join_vars) ++
       [mk_inst 50 STOP [] []]|>]
End


Theorem deep_join_family_ready:
  EVERY (\rev. EVERY (\n. codegen_ready_fn (deep_join_fn rev n))
    [15;16;17;18]) [F;T]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem deep_join_family_marker_free:
  EVERY (\rev. EVERY (\n.
    EVERY (\bb. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb.bb_instructions) (deep_join_fn rev n).fn_blocks)
    [15;16;17;18]) [F;T]
Proof
  EVAL_TAC
QED

Theorem deep_join_family_live_lengths:
  EVERY (\rev. EVERY (\n. LENGTH (input_vars_from "A"
    (THE (lookup_block "J" (deep_join_fn rev n).fn_blocks)).bb_instructions
    (live_vars_at (liveness_analyze (deep_join_fn rev n)) "J" 0)) = n)
    [15;16;17;18]) [F;T]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem deep_join_15_entry_some:
  IS_SOME (residual_matrix_step (deep_join_fn F 15) "E"
    (init_cleanup_plan_state NONE [] 0 0))
Proof
  EVAL_TAC
QED

