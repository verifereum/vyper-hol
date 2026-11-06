Theory fnLineageInvSpliceProbe
Ancestors fnPlanLineage fnLineageInvBoundary fnLineageInvLiteral codegenReadyCompute cfgTransform
  stackPlanGen stackPlanOps stackPlanTypes venomInst

(* Single-demand diagnostic candidate. Its intended burial mechanism is
   contradicted by splice_loop_h_second_optimistic_swap below: the planner
   promotes t back to the top after producing a. No retained spill is claimed. *)
Definition splice_loop_fn_def:
  splice_loop_fn =
    let vs = ["a";"b";"c";"d";"e";"f";"g";"h";"i";
              "j";"k";"l";"m";"n";"o";"p";"q";"r"] in
    mk_raw_function "splice_loop"
    [<|bb_label := "E"; bb_instructions :=
        [mk_inst 0 PARAM [Lit 0w] ["cond"]] ++
        MAPi (\i v. mk_inst (1+i) PARAM [Lit (n2w (1+i))] ["p_" ++ v]) vs ++
        [mk_inst 20 JMP [Label "H"] []]|>;
     <|bb_label := "H"; bb_instructions :=
        [mk_inst 21 ADD [Lit 1w; Lit 2w] ["t"]] ++
        MAPi (\i v. mk_inst (22+i) ADD [Lit (n2w i); Lit 1w] [v]) vs ++
        [mk_inst 41 MSTORE [Lit 0w; Var "t"] [];
         mk_inst 42 JNZ [Lit 1w; Label "B"; Label "Y"] []]|>;
     <|bb_label := "B"; bb_instructions :=
        MAPi (\i v. mk_inst (43+i) MSTORE [Lit (n2w i); Var v] []) vs ++
        [mk_inst 62 JNZ [Var "cond"; Label "L"; Label "X"] []]|>;
     <|bb_label := "L"; bb_instructions := [mk_inst 63 JMP [Label "H"] []]|>;
     <|bb_label := "X"; bb_instructions :=
        MAPi (\i v. mk_inst (64+i) MSTORE [Lit (n2w i); Var ("p_" ++ v)] []) vs ++
        [mk_inst 83 STOP [] []]|>;
     <|bb_label := "Y"; bb_instructions := [mk_inst 84 STOP [] []]|>]
End

Theorem splice_loop_ready:
  codegen_ready_fn splice_loop_fn
Proof
  EVAL_TAC >> simp[]
QED


(* Fixed-fixture computation, deliberately independent of the obsolete
   residual probe's readiness assertions. *)
Definition splice_loop_plan_def:
  splice_loop_plan lbl ps =
    generate_block_plan (liveness_analyze splice_loop_fn)
      (dfg_build_function splice_loop_fn) (cfg_analyze splice_loop_fn)
      splice_loop_fn (THE (lookup_block lbl splice_loop_fn.fn_blocks)) ps
End

Definition splice_loop_e_def:
  splice_loop_e = SND (THE (splice_loop_plan "E"
    (init_cleanup_plan_state NONE [] 0 0)))
End

Theorem splice_loop_e_exact[compute]:
  splice_loop_e = <|
    ps_stack := MAP Var ["p_r";"p_q";"p_p";"p_o";"p_n";"p_m";"p_l";"p_k";
      "p_j";"p_i";"p_h";"p_g";"p_f";"p_e";"p_d";"p_c";"p_b";"p_a";"cond"];
    ps_spilled := FEMPTY;
    ps_alloc := <|sa_free_slots :=
      [0;576;544;512;480;448;416;384;352;320;288;256;224;192;160;128;96;64;32];
      sa_next_offset := 608; sa_spill_base := 0|>;
    ps_label_counter := 0; ps_cleanup_height := NONE;
    ps_cleanup_growth := []; ps_cleanup_promised := F|>
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC
QED

Definition splice_loop_h_def:
  splice_loop_h = SND (THE (splice_loop_plan "H" splice_loop_e))
End


Theorem splice_loop_h_live_one:
  live_vars_at (liveness_analyze splice_loop_fn) "H" 1 =
    ["p_r";"p_q";"p_p";"p_o";"p_n";"p_m";"p_l";"p_k";
     "p_j";"p_i";"p_h";"p_g";"p_f";"p_e";"p_d";"p_c";"p_b";"p_a";"cond";"t"]
Proof
  EVAL_TAC
QED

Theorem splice_loop_h_first_add:
  generate_inst_plan (liveness_analyze splice_loop_fn)
    (dfg_build_function splice_loop_fn) (cfg_analyze splice_loop_fn)
    splice_loop_fn (mk_inst 21 ADD [Lit 1w; Lit 2w] ["t"])
    (live_vars_at (liveness_analyze splice_loop_fn) "H" 1) F F "H"
    splice_loop_e =
  SOME ([SOPush (Lit 2w); SOPush (Lit 1w); SOEmit "ADD"],
    splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"])
Proof
  `optimistic_swap_plan (dfg_build_function splice_loop_fn)
    (mk_inst 21 ADD [Lit 1w; Lit 2w] ["t"])
    (live_vars_at (liveness_analyze splice_loop_fn) "H" 1) F
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"]) =
    ([], splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"])` by
    (rewrite_tac[splice_loop_h_live_one, splice_loop_e_exact,
       optimistic_swap_plan_def, venomInstTheory.mk_inst_def] >> EVAL_TAC) >>
  `1w <> (2w:256 word)` by simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
  `MEM "t" (live_vars_at (liveness_analyze splice_loop_fn) "H" 1)` by
    simp[splice_loop_h_live_one] >>
  drule_all literal_add_inst_plan >>
  simp[release_dead_spills_def, splice_loop_e_exact, splice_loop_h_live_one] >>
  strip_tac >> first_x_assum irule
QED

Theorem splice_loop_h_live_two:
  live_vars_at (liveness_analyze splice_loop_fn) "H" 2 =
    ["p_r";"p_q";"p_p";"p_o";"p_n";"p_m";"p_l";"p_k";
     "p_j";"p_i";"p_h";"p_g";"p_f";"p_e";"p_d";"p_c";"p_b";"p_a";"cond";"a";"t"]
Proof
  EVAL_TAC
QED

Theorem splice_loop_h_a_t_inequivalent:
  ~operand_equiv (dfg_build_function splice_loop_fn) (Var "a") (Var "t")
Proof
  rewrite_tac[dfgDefsTheory.operand_equiv_def] >>
  simp[Once dfgDefsTheory.normalize_operand_def] >>
  EVAL_TAC
QED

Theorem splice_loop_h_second_optimistic_swap:
  optimistic_swap_plan (dfg_build_function splice_loop_fn)
    (mk_inst 22 ADD [Lit 0w; Lit 1w] ["a"])
    (live_vars_at (liveness_analyze splice_loop_fn) "H" 2) F
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Var "a"]) =
  ([SOSwap 1],
    splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "a"; Var "t"])
Proof
  simp[splice_loop_h_live_two, optimistic_swap_plan_def, venomInstTheory.mk_inst_def,
    splice_loop_h_a_t_inequivalent] >>
  rewrite_tac[splice_loop_e_exact] >> EVAL_TAC
QED
