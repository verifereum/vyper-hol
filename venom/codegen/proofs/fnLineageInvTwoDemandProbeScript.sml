Theory fnLineageInvTwoDemandProbe
Ancestors fnLineageInvSpliceProbe fnLineageInvLiteral stackPlanGen

(* The extra early output u uses the previously unused instruction ID 40.
   The two-demand store kills both early outputs; all other blocks and IDs
   are inherited unchanged from the checked single-demand candidate. *)
Definition splice_two_fn_def:
  splice_two_fn = splice_loop_fn with fn_blocks :=
    MAP (\bb. if bb.bb_label = "H" then
      bb with bb_instructions :=
        TAKE 1 bb.bb_instructions ++ [mk_inst 40 ADD [Lit 3w; Lit 4w] ["u"]] ++
        MAP (\inst. if inst.inst_id = 41 then
          mk_inst 41 MSTORE [Var "t"; Var "u"] [] else inst)
          (DROP 1 bb.bb_instructions)
      else bb) splice_loop_fn.fn_blocks
End

Theorem splice_two_ready:
  codegen_ready_fn splice_two_fn
Proof
  EVAL_TAC >> simp[]
QED

Theorem splice_two_t_u_inequivalent:
  ~operand_equiv (dfg_build_function splice_two_fn) (Var "t") (Var "u")
Proof
  rewrite_tac[dfgDefsTheory.operand_equiv_def] >>
  simp[Once dfgDefsTheory.normalize_operand_def] >> EVAL_TAC
QED

Theorem splice_two_live_observe:
  MAP (live_vars_at (liveness_analyze splice_two_fn) "H") [1;2;3;20;21] =
  MAP (\locals.
    ["p_r";"p_q";"p_p";"p_o";"p_n";"p_m";"p_l";"p_k";
     "p_j";"p_i";"p_h";"p_g";"p_f";"p_e";"p_d";"p_c";"p_b";"p_a";"cond"] ++ locals)
    [["t"]; ["u";"t"]; ["a";"u";"t"];
     ["r";"q";"p";"o";"n";"m";"l";"k";"j";"i";"h";"g";"f";"e";"d";"c";"b";"a";"u";"t"];
     ["r";"q";"p";"o";"n";"m";"l";"k";"j";"i";"h";"g";"f";"e";"d";"c";"b";"a"]]
Proof
  EVAL_TAC
QED

Theorem splice_two_first_add:
  generate_inst_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn)
    splice_two_fn (mk_inst 21 ADD [Lit 1w; Lit 2w] ["t"])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 1) F F "H"
    splice_loop_e =
  SOME ([SOPush (Lit 2w); SOPush (Lit 1w); SOEmit "ADD"],
    splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"])
Proof
  mp_tac splice_two_live_observe >> simp[] >> strip_tac >>
  `optimistic_swap_plan (dfg_build_function splice_two_fn)
    (mk_inst 21 ADD [Lit 1w; Lit 2w] ["t"])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 1) F
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"]) =
    ([], splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"])` by
    (asm_rewrite_tac[splice_loop_e_exact, optimistic_swap_plan_def,
       venomInstTheory.mk_inst_def] >> EVAL_TAC) >>
  `1w <> (2w:256 word)` by simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
  `MEM "t" (live_vars_at (liveness_analyze splice_two_fn) "H" 1)` by simp[] >>
  drule_all literal_add_inst_plan >>
  simp[stackPlanOpsTheory.release_dead_spills_def, splice_loop_e_exact] >>
  strip_tac >> first_x_assum irule
QED

Theorem splice_two_second_reorder_swap:
  reorder_one dfg [Lit 3w; Lit 4w] 0 (Lit 3w)
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 4w; Lit 3w]) =
  ([SOSwap 1], splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 3w; Lit 4w])
Proof
  rewrite_tac[splice_loop_e_exact, stackPlanOpsTheory.reorder_one_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``operand_equiv``, ``reduce_depth_plan``, ``do_swap``]) >>
  simp[dfgDefsTheory.operand_equiv_def, dfgDefsTheory.normalize_operand_def,
    wordsTheory.dimword_def, wordsTheory.n2w_11] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, wordsTheory.n2w_11] >> EVAL_TAC
QED

Theorem splice_two_second_reorder_noops:
  reorder_one dfg [Lit 3w; Lit 4w] 1 (Lit 4w)
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 3w; Lit 4w]) =
  ([], splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 3w; Lit 4w]) /\
  reorder_one dfg [Lit 4w; Lit 3w] 0 (Lit 4w)
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 4w; Lit 3w]) =
  ([], splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 4w; Lit 3w]) /\
  reorder_one dfg [Lit 4w; Lit 3w] 1 (Lit 3w)
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 4w; Lit 3w]) =
  ([], splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"; Lit 4w; Lit 3w])
Proof
  rewrite_tac[splice_loop_e_exact, stackPlanOpsTheory.reorder_one_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``operand_equiv``, ``reduce_depth_plan``, ``do_swap``]) >>
  simp[wordsTheory.dimword_def, wordsTheory.n2w_11] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``operand_equiv``, ``reduce_depth_plan``, ``do_swap``]) >>
  simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
  EVAL_TAC >> simp[wordsTheory.n2w_11, wordsTheory.dimword_def]
QED

Theorem splice_two_second_add:
  generate_inst_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn)
    splice_two_fn (mk_inst 40 ADD [Lit 3w; Lit 4w] ["u"])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 2) F F "H"
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"]) =
  SOME ([SOPush (Lit 4w); SOPush (Lit 3w); SOEmit "ADD"; SOSwap 1],
    splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "u"; Var "t"])
Proof
  mp_tac splice_two_live_observe >> simp[] >> strip_tac >>
  qabbrev_tac `ps0 = splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "t"]` >>
  `optimistic_swap_plan (dfg_build_function splice_two_fn)
    (mk_inst 40 ADD [Lit 3w; Lit 4w] ["u"])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 2) F
    (ps0 with ps_stack := ps0.ps_stack ++ [Var "u"]) =
    ([SOSwap 1], splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "u"; Var "t"])` by
    (simp[Abbr `ps0`] >>
     asm_rewrite_tac[optimistic_swap_plan_def, venomInstTheory.mk_inst_def] >>
     simp[splice_two_t_u_inequivalent] >>
     rewrite_tac[splice_loop_e_exact] >> EVAL_TAC) >>
  `3w <> (4w:256 word)` by simp[wordsTheory.n2w_11, wordsTheory.dimword_def] >>
  `MEM "u" (live_vars_at (liveness_analyze splice_two_fn) "H" 2)` by simp[] >>
  drule_all literal_add_inst_plan >>
  simp[stackPlanOpsTheory.release_dead_spills_def, splice_loop_e_exact] >>
  strip_tac >> first_x_assum irule
QED

Theorem splice_two_entry_result:
  ?ops. generate_block_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    (THE (lookup_block "E" splice_two_fn.fn_blocks))
    (init_cleanup_plan_state NONE [] 0 0) = SOME (ops, splice_loop_e)
Proof
  rewrite_tac[splice_loop_e_exact] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem splice_two_a_t_inequivalent:
  ~operand_equiv (dfg_build_function splice_two_fn) (Var "a") (Var "t")
Proof
  rewrite_tac[dfgDefsTheory.operand_equiv_def] >>
  simp[Once dfgDefsTheory.normalize_operand_def] >> EVAL_TAC
QED

Theorem splice_two_third_optimistic_swap:
  optimistic_swap_plan (dfg_build_function splice_two_fn)
    (mk_inst 22 ADD [Lit 0w; Lit 1w] ["a"])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 3) F
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "u"; Var "t"; Var "a"]) =
  ([SOSwap 1],
    splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "u"; Var "a"; Var "t"])
Proof
  mp_tac splice_two_live_observe >> simp[] >> strip_tac >>
  asm_rewrite_tac[optimistic_swap_plan_def, venomInstTheory.mk_inst_def] >>
  simp[splice_two_a_t_inequivalent] >>
  rewrite_tac[splice_loop_e_exact] >> EVAL_TAC
QED
