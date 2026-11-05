Theory fnPlanLineageDeepJoinProbe
Ancestors
  fnPlanLineageResidualProbe fnPlanLineagePhiTemporalProbe
  fnPlanLineageJoinEntry codegenReadyCompute fnPlanLineageStages
  stackPlanGen stackPlanOps stackPlanTypes stackModel venomInst cfgTransform
Libs wordsLib

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


Definition deep_join_15_entry_def:
  deep_join_15_entry =
   <|ps_stack :=
       [Var "v12"; Var "v00"; Var "v01"; Var "v02"; Var "v03"; Var "v04"; Var "v05"; Var "v06";
        Var "v07"; Var "v08"; Var "v09"; Var "v10"; Var "v11"]; ps_spilled := FEMPTY;
     ps_alloc := <|sa_free_slots := []; sa_next_offset := 0; sa_spill_base := 0|>;
     ps_label_counter := 0; ps_cleanup_height := NONE; ps_cleanup_growth := [];
     ps_cleanup_promised := F|>
End

Theorem deep_join_15_entry_exact:
  residual_matrix_step (deep_join_fn F 15) "E"
    (init_cleanup_plan_state NONE [] 0 0) =
  SOME ([SOLabel "E"; SOSwap 13; SOPushLabel "A"; SOEmit "JUMPI";
         SOPushLabel "B"; SOEmit "JUMP"], deep_join_15_entry)
Proof
  EVAL_TAC
QED

Theorem deep_join_15_a_clean:
  clean_stack_plan (liveness_analyze (deep_join_fn F 15))
    (cfg_analyze (deep_join_fn F 15)) (deep_join_fn F 15)
    (THE (lookup_block "A" (deep_join_fn F 15).fn_blocks))
    deep_join_15_entry = ([], deep_join_15_entry)
Proof
  rewrite_tac[deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_15_a_first:
  generate_inst_plan (liveness_analyze (deep_join_fn F 15))
    (dfg_build_function (deep_join_fn F 15)) (cfg_analyze (deep_join_fn F 15))
    (deep_join_fn F 15) (mk_inst 21 ADD [Lit 1w; Lit 2w] ["a0"])
    (live_vars_at (liveness_analyze (deep_join_fn F 15)) "A" 1)
    F F "A" deep_join_15_entry =
    SOME ([SOPush (Lit 2w); SOPush (Lit 1w); SOEmit "ADD"],
      deep_join_15_entry with ps_stack := deep_join_15_entry.ps_stack ++ [Var "a0"])
Proof
  rewrite_tac[deep_join_15_entry_def] >> EVAL_TAC
QED

Definition deep_join_15_a_def:
  deep_join_15_a = deep_join_15_entry with ps_stack :=
    [Var "r"; Var "v12"; Var "v11"; Var "v10"; Var "v09"; Var "v08"; Var "v07"; Var "v06";
     Var "v05"; Var "v04"; Var "v03"; Var "v02"; Var "v01"; Var "v00"; Var "a1"; Var "a0"]
End

Theorem deep_join_15_a_exact:
  residual_matrix_step (deep_join_fn F 15) "A" deep_join_15_entry =
  SOME ([SOLabel "A"; SOPush (Lit 2w); SOPush (Lit 1w); SOEmit "ADD";
    SOPush (Lit 4w); SOPush (Lit 3w); SOEmit "ADD"; SOSwap 1;
    SOPushOfst "J" 0; SOSwap 15; SOSwap 14; SOSwap 3; SOSwap 13; SOSwap 4;
    SOSwap 12; SOSwap 5; SOSwap 11; SOSwap 6; SOSwap 10; SOSwap 7; SOSwap 9;
    SOSwap 7; SOSwap 6; SOSwap 5; SOSwap 4; SOSwap 3; SOSwap 2; SOSwap 1;
    SOPushLabel "J"; SOEmit "JUMP"], deep_join_15_a)
Proof
  rewrite_tac[deep_join_15_a_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Definition deep_join_15_b_def:
  deep_join_15_b = deep_join_15_entry with ps_stack :=
    [Var "v12"; Var "v11"; Var "v10"; Var "v09"; Var "v08"; Var "v07"; Var "v06";
     Var "v05"; Var "v04"; Var "v03"; Var "v02"; Var "v01"; Var "v00"; Var "b1"; Var "b0"]
End

Theorem deep_join_15_b_exact:
  residual_matrix_step (deep_join_fn F 15) "B" deep_join_15_entry =
  SOME ([SOLabel "B"; SOPush (Lit 6w); SOPush (Lit 5w); SOEmit "ADD";
    SOPush (Lit 8w); SOPush (Lit 7w); SOEmit "ADD"; SOSwap 2; SOSwap 13;
    SOSwap 3; SOSwap 12; SOSwap 4; SOSwap 11; SOSwap 5; SOSwap 10; SOSwap 6;
    SOSwap 9; SOSwap 7; SOSwap 8; SOSwap 7; SOSwap 6; SOSwap 5; SOSwap 4;
    SOSwap 3; SOSwap 2; SOSwap 1; SOPushLabel "J"; SOEmit "JUMP"], deep_join_15_b)
Proof
  rewrite_tac[deep_join_15_b_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_family_whole_some:
  EVERY (\rev. EVERY (\n. IS_SOME (generate_fn_plan_with_cleanup_analyzed
    (liveness_analyze (deep_join_fn rev n)) (dfg_build_function (deep_join_fn rev n))
    (cfg_analyze (deep_join_fn rev n)) NONE [] (deep_join_fn rev n) 0 0))
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

Definition deep_join_18_entry_def:
  deep_join_18_entry = deep_join_15_entry with ps_stack :=
    [Var "v15"; Var "v00"; Var "v01"; Var "v02"; Var "v03"; Var "v04"; Var "v05"; Var "v06";
     Var "v07"; Var "v08"; Var "v09"; Var "v10"; Var "v11"; Var "v12"; Var "v13"; Var "v14"]
End

Theorem deep_join_18_entry_exact:
  residual_matrix_step (deep_join_fn F 18) "E"
    (init_cleanup_plan_state NONE [] 0 0) =
  SOME ([SOLabel "E"; SOSwap 16; SOPushLabel "A"; SOEmit "JUMPI";
         SOPushLabel "B"; SOEmit "JUMP"], deep_join_18_entry)
Proof
  rewrite_tac[deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Definition deep_join_18_a_def:
  deep_join_18_a = deep_join_18_entry with <|
    ps_stack := [Var "r"; Var "v15"; Var "v14"; Var "v13"; Var "v12"; Var "v11"; Var "v10";
      Var "v09"; Var "v08"; Var "v07"; Var "v06"; Var "v05"; Var "v04"; Var "v03";
      Var "v02"; Var "v01"; Var "v00"; Var "a1"; Var "a0"];
    ps_alloc := <|sa_free_slots :=
      [0;576;544;512;480;448;416;384;352;320;288;256;224;192;160;128;96;64;32];
      sa_next_offset := 608; sa_spill_base := 0|> |>
End

Theorem deep_join_18_a_state:
  OPTION_MAP SND (residual_matrix_step (deep_join_fn F 18) "A" deep_join_18_entry) =
    SOME deep_join_18_a
Proof
  rewrite_tac[deep_join_18_a_def, deep_join_18_entry_def, deep_join_15_entry_def] >>
  EVAL_TAC
QED

Definition deep_join_18_b_def:
  deep_join_18_b = deep_join_18_entry with ps_stack :=
    [Var "v15"; Var "v14"; Var "v13"; Var "v12"; Var "v11"; Var "v10";
      Var "v09"; Var "v08"; Var "v07"; Var "v06"; Var "v05"; Var "v04"; Var "v03";
      Var "v02"; Var "v01"; Var "v00"; Var "b1"; Var "b0"]
End

Theorem deep_join_18_b_state:
  OPTION_MAP SND (residual_matrix_step (deep_join_fn F 18) "B" deep_join_18_entry) =
    SOME deep_join_18_b
Proof
  rewrite_tac[deep_join_18_b_def, deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

(* These independent predecessor runs expose different scratch allocator histories;
   the frozen lineage splice must use DFS global fields, not this B allocator. *)
Theorem deep_join_18_entry_observations:
  deep_join_18_a.ps_spilled = FEMPTY /\ deep_join_18_b.ps_spilled = FEMPTY /\
  deep_join_18_a.ps_alloc.sa_next_offset = 608 /\
  deep_join_18_b.ps_alloc.sa_next_offset = 0 /\
  HD deep_join_18_a.ps_stack = Var "r"
Proof
  rewrite_tac[deep_join_18_a_def, deep_join_18_b_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Definition deep_join_18_join_ops_def:
  deep_join_18_join_ops = [SOLabel "J"; SOPoke 0 (Var "x0"); SOPoke 1 (Var "x1")] ++
    FLAT (GENLIST (\i. [SOPush (Lit (n2w i)); SOEmit "MSTORE"]) 18) ++ [SOEmit "STOP"]
End

Theorem deep_join_18_join_a_result:
  residual_matrix_step (deep_join_fn F 18) "J" deep_join_18_a =
  SOME (deep_join_18_join_ops, deep_join_18_a with ps_stack := [Var "r"])
Proof
  rewrite_tac[deep_join_18_join_ops_def, deep_join_18_a_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_18_join_spliced_replay:
  residual_matrix_step (deep_join_fn F 18) "J"
    (deep_join_18_a with <|ps_stack := deep_join_18_b.ps_stack;
                         ps_spilled := deep_join_18_b.ps_spilled|>) =
  SOME (deep_join_18_join_ops, deep_join_18_a with ps_stack := [])
Proof
  rewrite_tac[deep_join_18_join_ops_def, deep_join_18_a_def, deep_join_18_b_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Definition deep_join_18_a_pre_def:
  deep_join_18_a_pre = deep_join_18_entry with ps_stack :=
    deep_join_18_entry.ps_stack ++ [Var "a1"; Var "a0"; Var "r"]
End

Theorem deep_join_18_a_prefix:
  OPTION_MAP SND (generate_block_insts_plan
    (liveness_analyze (deep_join_fn F 18)) (dfg_build_function (deep_join_fn F 18))
    (cfg_analyze (deep_join_fn F 18)) (deep_join_fn F 18) "A" F 0 4 0
    [mk_inst 21 ADD [Lit 1w; Lit 2w] ["a0"];
     mk_inst 22 ADD [Lit 3w; Lit 4w] ["a1"];
     mk_inst 23 OFFSET [Lit 0w; Label "J"] ["r"]] deep_join_18_entry) =
    SOME deep_join_18_a_pre
Proof
  rewrite_tac[deep_join_18_a_pre_def, deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Definition deep_join_18_targets_def:
  deep_join_18_targets =
    [Var "v15"; Var "v14"; Var "v13"; Var "v12"; Var "v11"; Var "v10";
     Var "v09"; Var "v08"; Var "v07"; Var "v06"; Var "v05"; Var "v04"; Var "v03";
     Var "v02"; Var "v01"; Var "v00"; Var "a1"; Var "a0"]
End

Theorem deep_join_18_a_target:
  join_target_ops (liveness_analyze (deep_join_fn F 18)) (deep_join_fn F 18)
    "A" (mk_inst 24 JMP [Label "J"] []) = SOME deep_join_18_targets
Proof
  rewrite_tac[deep_join_18_targets_def] >> EVAL_TAC
QED

Theorem deep_join_18_a_restore:
  restore_spilled_plan deep_join_18_targets deep_join_18_a_pre = ([], deep_join_18_a_pre)
Proof
  rewrite_tac[deep_join_18_targets_def, deep_join_18_a_pre_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_18_a_reorder:
  SND (reorder_plan (dfg_build_function (deep_join_fn F 18))
    deep_join_18_targets deep_join_18_a_pre) = deep_join_18_a
Proof
  rewrite_tac[deep_join_18_targets_def, deep_join_18_a_pre_def, deep_join_18_a_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_18_a_release:
  release_dead_spills (live_vars_at (liveness_analyze (deep_join_fn F 18)) "A" 4)
    deep_join_18_a = deep_join_18_a
Proof
  rewrite_tac[deep_join_18_a_def, deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Definition deep_join_18_phi0_def:
  deep_join_18_phi0 ps = ps with ps_stack :=
    TAKE (LENGTH ps.ps_stack - 1) ps.ps_stack ++ [Var "x0"]
End

Definition deep_join_18_phi1_def:
  deep_join_18_phi1 ps = ps with ps_stack :=
    TAKE (LENGTH ps.ps_stack - 2) ps.ps_stack ++ [Var "x1"; Var "x0"]
End

Theorem deep_join_18_phi_steps:
  EVERY (\ps.
    generate_phi_plan
      (mk_inst 28 PHI [Label "A"; Var "a0"; Label "B"; Var "b0"] ["x0"])
      (live_vars_at (liveness_analyze (deep_join_fn F 18)) "J" 1) T ps =
      ([SOPoke 0 (Var "x0")], deep_join_18_phi0 ps) /\
    generate_phi_plan
      (mk_inst 29 PHI [Label "A"; Var "a1"; Label "B"; Var "b1"] ["x1"])
      (live_vars_at (liveness_analyze (deep_join_fn F 18)) "J" 2) T
      (deep_join_18_phi0 ps) =
      ([SOPoke 1 (Var "x1")], deep_join_18_phi1 ps))
    [deep_join_18_a; deep_join_18_a with ps_stack := deep_join_18_b.ps_stack]
Proof
  rewrite_tac[deep_join_18_phi0_def, deep_join_18_phi1_def, deep_join_18_a_def,
    deep_join_18_b_def, deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

(* The actual second successor has the first successor's high-water mark,
   but the parent's free list. This is not the independent B run above. *)
Definition deep_join_18_b_start_def:
  deep_join_18_b_start = deep_join_18_entry with ps_alloc :=
    <|sa_free_slots := []; sa_next_offset := 608; sa_spill_base := 0|>
End

Theorem deep_join_18_actual_b:
  OPTION_MAP SND (residual_matrix_step (deep_join_fn F 18) "B" deep_join_18_b_start) =
    SOME (deep_join_18_b_start with ps_stack := deep_join_18_b.ps_stack)
Proof
  rewrite_tac[deep_join_18_b_start_def, deep_join_18_b_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_18_actual_a_subtree:
  OPTION_MAP (\(ops,visited,ps). (visited,ps))
    (generate_fn_plan_aux (liveness_analyze (deep_join_fn F 18))
      (dfg_build_function (deep_join_fn F 18)) (cfg_analyze (deep_join_fn F 18))
      (deep_join_fn F 18) ["A"] ["E"] deep_join_18_entry) =
    SOME (["J";"A";"E"], deep_join_18_a)
Proof
  rewrite_tac[deep_join_18_a_def, deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_18_second_successor_start:
  (deep_join_18_entry with <|
     ps_alloc := deep_join_18_a.ps_alloc with
       sa_free_slots := deep_join_18_entry.ps_alloc.sa_free_slots;
     ps_label_counter := deep_join_18_a.ps_label_counter|>) = deep_join_18_b_start
Proof
  rewrite_tac[deep_join_18_a_def, deep_join_18_b_start_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED

Theorem deep_join_18_lineage_splice:
  (deep_join_18_a with <|
    ps_stack := (deep_join_18_b_start with ps_stack := deep_join_18_b.ps_stack).ps_stack;
    ps_spilled := (deep_join_18_b_start with ps_stack := deep_join_18_b.ps_stack).ps_spilled|>) =
  (deep_join_18_a with <|ps_stack := deep_join_18_b.ps_stack;
                        ps_spilled := deep_join_18_b.ps_spilled|>)
Proof
  rewrite_tac[deep_join_18_a_def, deep_join_18_b_def, deep_join_18_b_start_def,
    deep_join_18_entry_def, deep_join_15_entry_def] >> EVAL_TAC
QED


Theorem deep_join_family_entry_some:
  EVERY (\rev. EVERY (\n. IS_SOME (residual_matrix_step (deep_join_fn rev n) "E"
    (init_cleanup_plan_state NONE [] 0 0))) [15;16;17;18]) [F;T]
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

Definition deep_join_family_entry_def:
  deep_join_family_entry rev n = SND (THE (residual_matrix_step (deep_join_fn rev n) "E"
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem deep_join_family_arms_some:
  EVERY (\rev. EVERY (\n. EVERY (\lbl.
    IS_SOME (residual_matrix_step (deep_join_fn rev n) lbl (deep_join_family_entry rev n)))
    ["A";"B"]) [15;16;17;18]) [F;T]
Proof
  simpLib.SIMP_TAC bool_ss [listTheory.EVERY_DEF] >> rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >> EVAL_TAC
QED

(* All eight whole runs and independent E/A/B stages are SOME. Exact F18
   stages show scratch spills on A's reorder, empty persistent maps,
   high-water mark 608, and an unmarked residual r. B uses no scratch slots.
   The checked first-subtree and second-successor-start equations distinguish
   actual DFS global fields from independently computed predecessor fields.
   Splicing B's physical fields into A's DFS join entry preserves both join
   operations and allocation; both PHIs have the same depth 0/1 behavior.
   This finite observation does not prove the frozen reachability predicates
   or a universal physical-state invariant. The remaining family-wide
   spliced replay checks should use cached arm states rather than nested EVAL.
*)
