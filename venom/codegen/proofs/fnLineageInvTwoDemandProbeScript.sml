Theory fnLineageInvTwoDemandProbe
Ancestors fnLineageInvSpliceProbe fnLineageInvLiteral fnPlanPrefix fnPlanLineageReplay fnPlanLineage stackPlanGen

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


Theorem splice_two_indexed_data:
  !vs. vs = ["a";"b";"c";"d";"e";"f";"g";"h";"i";
                 "j";"k";"l";"m";"n";"o";"p";"q";"r"] ==> !k. k < 18 ==>
  EL (k+2) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions =
    mk_inst (22+k) ADD [Lit (n2w k); Lit 1w] [EL k vs] /\
  live_vars_at (liveness_analyze splice_two_fn) "H" (k+3) =
    ["p_r";"p_q";"p_p";"p_o";"p_n";"p_m";"p_l";"p_k";
     "p_j";"p_i";"p_h";"p_g";"p_f";"p_e";"p_d";"p_c";"p_b";"p_a";"cond"] ++
    REVERSE (TAKE (k+1) vs) ++ ["u";"t"] /\
  ~operand_equiv (dfg_build_function splice_two_fn) (Var (EL k vs)) (Var "t") /\
  DROP (k+2) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions =
    EL (k+2) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions ::
    DROP (k+3) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions /\
  DROP (k+3) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions <> [] /\
  ~is_terminator (HD (DROP (k+3)
    (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions)).inst_opcode
Proof
  gen_tac >> disch_then SUBST1_TAC >>
  (* One bounded evaluation per step keeps each kernel computation small. *)
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >> EVAL_TAC >> simp[]
QED

Theorem splice_two_indexed_optimistic:
  !vs. vs = ["a";"b";"c";"d";"e";"f";"g";"h";"i";
                 "j";"k";"l";"m";"n";"o";"p";"q";"r"] ==> !k. k < 18 ==>
  optimistic_swap_plan (dfg_build_function splice_two_fn)
    (mk_inst (22+k) ADD [Lit (n2w k); Lit 1w] [EL k vs])
    (live_vars_at (liveness_analyze splice_two_fn) "H" (k+3)) F
    (splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE k vs) ++ [Var "t"; Var (EL k vs)]) =
    ([SOSwap 1], splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE (k+1) vs) ++ [Var "t"]) /\
  release_dead_spills (live_vars_at (liveness_analyze splice_two_fn) "H" (k+3))
    (splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE (k+1) vs) ++ [Var "t"]) =
    (splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE (k+1) vs) ++ [Var "t"])
Proof
  gen_tac >> disch_then SUBST1_TAC >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV ALL_CONV) >>
  conj_tac >- (conj_tac >>
    pure_rewrite_tac[EVAL ``liveness_analyze splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
    pure_rewrite_tac[EVAL ``splice_loop_e``] >> EVAL_TAC >> simp[]) >> simp[]
QED

Theorem splice_two_indexed_step:
  !vs k. vs = ["a";"b";"c";"d";"e";"f";"g";"h";"i";
                 "j";"k";"l";"m";"n";"o";"p";"q";"r"] /\ k < 18 ==>
  generate_inst_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    (EL (k+2) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions)
    (live_vars_at (liveness_analyze splice_two_fn) "H" (k+3)) F F "H"
    (splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE k vs) ++ [Var "t"]) =
  SOME ([SOPush (Lit 1w); SOPush (Lit (n2w k)); SOEmit "ADD"; SOSwap 1],
    splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE (k+1) vs) ++ [Var "t"])
Proof
  rpt strip_tac >>
  drule splice_two_indexed_data >> disch_then (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule splice_two_indexed_optimistic >> disch_then (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH vs = 18` by simp[] >>
  qpat_x_assum `vs = _` kall_tac >>
  `MEM (EL k vs) (live_vars_at (liveness_analyze splice_two_fn) "H" (k+3))` by
    (`MEM (EL k vs) (TAKE (k+1) vs)` by
       (simp[IgnAsm `vs = _`, listTheory.MEM_EL] >> qexists_tac `k` >>
        simp[IgnAsm `vs = _`, listTheory.EL_TAKE]) >>
     simp[IgnAsm `vs = _`]) >>
  qmatch_goalsub_abbrev_tac `generate_inst_plan _ _ _ _ _ _ _ _ _ ps0` >>
  `optimistic_swap_plan (dfg_build_function splice_two_fn)
    (mk_inst (22+k) ADD [Lit (n2w k); Lit 1w] [EL k vs])
    (live_vars_at (liveness_analyze splice_two_fn) "H" (k+3)) F
    (ps0 with ps_stack := ps0.ps_stack ++ [Var (EL k vs)]) =
    ([SOSwap 1], splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE (k+1) vs) ++ [Var "t"])` by
    (qpat_x_assum `optimistic_swap_plan _ _ _ _ _ = _` mp_tac >>
     simp[Abbr `ps0`] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
     simp[]) >>
  drule_all literal_add_inst_plan >> simp[IgnAsm `vs = _`]
QED

Theorem splice_two_indexed_prefix:
  !vs. vs = ["a";"b";"c";"d";"e";"f";"g";"h";"i";
                 "j";"k";"l";"m";"n";"o";"p";"q";"r"] ==>
  !j k. k+j <= 18 ==>
  ?ops. generate_block_insts_prefix (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    "H" F 0 22 (k+2) j
    (DROP (k+2) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions)
    (splice_loop_e with ps_stack :=
      splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE k vs) ++ [Var "t"]) =
  SOME (ops, splice_loop_e with ps_stack :=
    splice_loop_e.ps_stack ++ [Var "u"] ++ MAP Var (TAKE (k+j) vs) ++ [Var "t"])
Proof
  gen_tac >> strip_tac >> Induct
  >- simp[generate_block_insts_prefix_def] >>
  rpt strip_tac >>
  `k < 18` by decide_tac >>
  drule splice_two_indexed_data >> disch_then (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `k+1+j <= 18` by decide_tac >>
  first_x_assum (qspec_then `k+1` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all splice_two_indexed_step >> strip_tac >>
  qpat_x_assum `vs = _` kall_tac >>
  qpat_x_assum `DROP _ _ = _` (fn th => once_rewrite_tac[th]) >>
  Cases_on `DROP (k+3) (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions`
  >- gvs[] >>
  qpat_x_assum `EL _ _ = _` kall_tac >>
  qpat_x_assum `live_vars_at _ _ _ = _` kall_tac >>
  fs[] >> simp[Once generate_block_insts_prefix_def] >>
  `j+(k+1) = k+SUC j` by decide_tac >> simp[]
QED

Theorem splice_two_demand_result:
  generate_inst_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    (mk_inst 41 MSTORE [Var "t"; Var "u"] [])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 21) F T "H"
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "u"] ++
      MAP Var ["a";"b";"c";"d";"e";"f";"g";"h";"i";
               "j";"k";"l";"m";"n";"o";"p";"q";"r"] ++ [Var "t"]) =
  SOME ([SOSwap 2; SOSpill 32; SOSwap 2; SOSpill 64; SOSwap 2; SOSpill 96;
         SOSwap 16; SOSwap 1; SOEmit "MSTORE"],
    splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |>)
Proof
  mp_tac splice_two_live_observe >> simp[] >> strip_tac >>
  asm_rewrite_tac[] >>
  CONV_TAC (RHS_CONV EVAL) >>
  pure_rewrite_tac[EVAL ``splice_loop_e``] >> simp[] >>
  pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``release_dead_spills``]) >>
  irule release_dead_spills_live_domain >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem splice_two_suffix_result:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops. generate_block_insts_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    "H" F 0 22 20
    (DROP 20 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions)
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "u"] ++
      MAP Var ["a";"b";"c";"d";"e";"f";"g";"h";"i";
               "j";"k";"l";"m";"n";"o";"p";"q";"r"] ++ [Var "t"]) = SOME (ops,q)
Proof
  gen_tac >> strip_tac >>
  `DROP 20 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions =
    [mk_inst 41 MSTORE [Var "t"; Var "u"] [];
     mk_inst 42 JNZ [Lit 1w; Label "B"; Label "Y"] []]` by EVAL_TAC >>
  asm_rewrite_tac[] >>
  simp[Once generate_block_insts_plan_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def] >>
  mp_tac splice_two_demand_result >> simp[venomInstTheory.mk_inst_def] >>
  strip_tac >> asm_rewrite_tac[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``release_dead_spills``]) >>
  simp[] >> sym_tac >> irule release_dead_spills_live_domain >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem splice_two_tail_result:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops. generate_block_insts_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    "H" F 0 22 2
    (DROP 2 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions)
    (splice_loop_e with ps_stack := splice_loop_e.ps_stack ++ [Var "u";Var "t"]) = SOME (ops,q)
Proof
  gen_tac >> strip_tac >>
  drule splice_two_suffix_result >> strip_tac >>
  qpat_x_assum `q = _` kall_tac >>
  qspec_then `["a";"b";"c";"d";"e";"f";"g";"h";"i";
                 "j";"k";"l";"m";"n";"o";"p";"q";"r"]` mp_tac splice_two_indexed_prefix >>
  simp[] >> disch_then (qspecl_then [`18`,`0`] mp_tac) >> simp[] >> strip_tac >>
  `LENGTH (DROP 2 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions) = 20`
    by EVAL_TAC >>
  qspec_then `18` (fn th => simp[th]) generate_block_insts_plan_split >>
  rule_assum_tac (PURE_REWRITE_RULE
    [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND, listTheory.MAP]) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  first_assum (irule_at Any) >>
  `DROP 18 (DROP 2 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions) =
   DROP 20 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions` by EVAL_TAC >>
  asm_rewrite_tac[] >> qexists_tac `ops` >> simp[]
QED

Theorem splice_two_insts_result:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops. generate_block_insts_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    "H" F 0 22 0
    (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions
    splice_loop_e = SOME (ops,q)
Proof
  gen_tac >> strip_tac >> drule splice_two_tail_result >> strip_tac >>
  qpat_x_assum `q = _` kall_tac >>
  ` (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions =
      mk_inst 21 ADD [Lit 1w;Lit 2w] ["t"] ::
      mk_inst 40 ADD [Lit 3w;Lit 4w] ["u"] ::
      DROP 2 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions` by EVAL_TAC >>
  `?rest. DROP 2 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions =
      mk_inst 22 ADD [Lit 0w;Lit 1w] ["a"] :: rest` by (qexists_tac `DROP 3 (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions` >> EVAL_TAC) >>
  once_asm_rewrite_tac[] >>
  simp[Once generate_block_insts_plan_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, splice_two_first_add] >>
  simp[Once generate_block_insts_plan_def, venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def, splice_two_second_add] >>
  qpat_x_assum `generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  gvs[venomInstTheory.mk_inst_def,
      SRULE [venomInstTheory.mk_inst_def] splice_two_second_add] >>
  qpat_x_assum `SOME _ = generate_block_insts_plan _ _ _ _ _ _ _ _ _ _ _`
    (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Theorem splice_two_block_result:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops. generate_block_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    (THE (lookup_block "H" splice_two_fn.fn_blocks)) splice_loop_e = SOME (ops,q)
Proof
  gen_tac >> strip_tac >> drule splice_two_insts_result >> strip_tac >>
  qpat_x_assum `q = _` kall_tac >>
  `!bb. bb = THE (lookup_block "H" splice_two_fn.fn_blocks) ==>
     bb <> HD splice_two_fn.fn_blocks /\
     LENGTH (cfg_preds_of (cfg_analyze splice_two_fn) bb.bb_label) <> 1 /\
     non_param_insts bb = bb.bb_instructions /\
     ~bb_is_halting bb /\ LENGTH (get_params bb.bb_instructions) = 0 /\
     LENGTH bb.bb_instructions = 22 /\ bb.bb_label = "H" /\
     (!ops. ~revert_block_spills bb ops)` by (rw[] >> EVAL_TAC >> simp[]) >>
  first_x_assum (qspec_then `THE (lookup_block "H" splice_two_fn.fn_blocks)` mp_tac) >>
  simp[] >> strip_tac >>
  simp[generate_block_plan_def] >> qexists_tac `SOLabel "H" :: ops` >> simp[]
QED

(* Finite observation only: the three spills survive the block, but the
   resulting state has bounded spill slots and exact live inventory.
   This does not establish marked layout or the DFS/lineage splice premises. *)
Theorem splice_two_final_observe:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  plan_slots_bounded 0 q /\
  set q.ps_stack UNION FDOM q.ps_spilled =
    set (MAP Var (live_vars_at (liveness_analyze splice_two_fn) "H" 22))
Proof
  gen_tac >> strip_tac >> gvs[] >> conj_tac
  >- (EVAL_TAC >> rpt gen_tac >>
      rpt (IF_CASES_TAC >> gvs[])) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``set``]) >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem splice_two_schedule:
  fn_entry_label splice_two_fn = SOME "E" /\
  cfg_succs_of (cfg_analyze splice_two_fn) "E" = ["H"] /\
  cfg_succs_of (cfg_analyze splice_two_fn) "H" = ["Y";"B"] /\
  lookup_block "E" splice_two_fn.fn_blocks =
    SOME (THE (lookup_block "E" splice_two_fn.fn_blocks)) /\
  lookup_block "H" splice_two_fn.fn_blocks =
    SOME (THE (lookup_block "H" splice_two_fn.fn_blocks))
Proof
  EVAL_TAC
QED

Theorem splice_two_dfs_h:
  dfs_aux_call (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    ["H"] ["E"] splice_loop_e
Proof
  mp_tac splice_two_entry_result >> strip_tac >>
  `dfs_aux_call (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    ["E"] [] (init_cleanup_plan_state NONE [] 0 0)` by
    (irule dfs_aux_call_entry >> simp[splice_two_schedule]) >>
  mp_tac splice_two_schedule >> strip_tac >>
  drule dfs_aux_call_succs >>
  disch_then (qspec_then `THE (lookup_block "E" splice_two_fn.fn_blocks)` mp_tac) >>
  simp[] >> strip_tac >>
  drule dfs_aux_call_branch >> simp[]
QED

Theorem splice_two_lineage_h:
  lineage_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    "H" splice_loop_e
Proof
  mp_tac splice_two_entry_result >> strip_tac >>
  mp_tac splice_two_schedule >> strip_tac >>
  `dfs_block_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    "H" splice_loop_e` by
    (simp[dfs_block_state_def] >> qexistsl_tac [`[]`,`["E"]`] >> simp[splice_two_dfs_h]) >>
  `lineage_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    "E" (init_cleanup_plan_state NONE [] 0 0)` by
    (irule lineage_state_entry >> simp[]) >>
  `dfs_block_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    "E" (init_cleanup_plan_state NONE [] 0 0)` by
    (simp[dfs_block_state_def] >> qexistsl_tac [`[]`,`[]`] >> simp[dfs_aux_call_entry]) >>
  `lineage_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    "H" (splice_loop_e with <|ps_stack := splice_loop_e.ps_stack;
                              ps_spilled := splice_loop_e.ps_spilled|>)` suffices_by simp[] >>
  irule lineage_state_step >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`NONE`,`F`] >> gvs[init_cleanup_plan_state_def]
QED


Theorem splice_two_y_data:
  lookup_block "Y" splice_two_fn.fn_blocks =
    SOME <|bb_label := "Y"; bb_instructions := [mk_inst 84 STOP [] []]|> /\
  cfg_preds_of (cfg_analyze splice_two_fn) "Y" = ["H"] /\
  cfg_succs_of (cfg_analyze splice_two_fn) "Y" = [] /\
  live_vars_at (liveness_analyze splice_two_fn) "Y" 0 = [] /\
  live_vars_at (liveness_analyze splice_two_fn) "Y" 1 = [] /\
  input_vars_from "H" [mk_inst 84 STOP [] []] [] = [] /\
  (THE (lookup_block "Y" splice_two_fn.fn_blocks)) <> HD splice_two_fn.fn_blocks
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem splice_two_y_cleanup:
  !q. q.ps_cleanup_height = NONE /\ ~q.ps_cleanup_promised ==>
  clean_stack_plan (liveness_analyze splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn
    (THE (lookup_block "Y" splice_two_fn.fn_blocks)) q =
    popmany_plan (MAP Var (live_vars_at (liveness_analyze splice_two_fn) "H" 22)) q
Proof
  rpt strip_tac >>
  `LENGTH (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions = 22` by EVAL_TAC >>
  simp[clean_stack_plan_def, splice_two_y_data, splice_two_schedule,
       cleanup_elision_safe_without_height] >>
  once_rewrite_tac[cj 5 splice_two_schedule] >> simp[]
QED

Theorem splice_two_h_end_live:
  live_vars_at (liveness_analyze splice_two_fn) "H" 22 =
  ["p_r";"p_q";"p_p";"p_o";"p_n";"p_m";"p_l";"p_k";"p_j";"p_i";"p_h";"p_g";"p_f";"p_e";"p_d";"p_c";"p_b";"p_a";"cond";
   "r";"q";"p";"o";"n";"m";"l";"k";"j";"i";"h";"g";"f";"e";"d";"c";"b";"a"]
Proof
  EVAL_TAC
QED

Theorem splice_two_y_pop:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops. popmany_plan (MAP Var (live_vars_at (liveness_analyze splice_two_fn) "H" 22)) q =
    (ops,q with ps_stack := [])
Proof
  rpt strip_tac >> gvs[] >> rewrite_tac[splice_two_h_end_live] >>
  pure_rewrite_tac[EVAL ``splice_loop_e``] >> simp[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  pure_once_rewrite_tac[sortingTheory.QSORT_DEF] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``QSORT``, ``FOLDL``]) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``FOLDL``]) >>
  EVAL_TAC >> simp[]
QED

Theorem splice_two_y_block:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops r. generate_block_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    (THE (lookup_block "Y" splice_two_fn.fn_blocks)) q = SOME (ops,r) /\
    r.ps_alloc.sa_next_offset = 608 /\ r.ps_alloc.sa_spill_base = 0 /\ r.ps_label_counter = 0
Proof
  gen_tac >> strip_tac >> drule splice_two_y_pop >> strip_tac >>
  `q.ps_cleanup_height = NONE /\ ~q.ps_cleanup_promised` by
    (gvs[] >> EVAL_TAC) >>
  drule_all splice_two_y_cleanup >> strip_tac >>
  `non_param_insts (THE (lookup_block "Y" splice_two_fn.fn_blocks)) = [mk_inst 84 STOP [] []] /\
   bb_is_halting (THE (lookup_block "Y" splice_two_fn.fn_blocks)) /\
   get_params (THE (lookup_block "Y" splice_two_fn.fn_blocks)).bb_instructions = [] /\
   (!ops. ~revert_block_spills (THE (lookup_block "Y" splice_two_fn.fn_blocks)) ops)` by
    (EVAL_TAC >> simp[]) >>
  `<|bb_label := "Y"; bb_instructions := [mk_inst 84 STOP [] []]|> <> HD splice_two_fn.fn_blocks` by EVAL_TAC >>
  gvs[splice_two_y_data] >>
  qpat_x_assum `(ops,_) = popmany_plan _ _` (assume_tac o SYM) >>
  simp[generate_block_plan_def, splice_two_y_data,
       generate_block_insts_plan_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``liveness_analyze``, ``dfg_build_function``, ``cfg_analyze``, ``splice_two_fn``,
     ``release_dead_spills``]) >>
  simp[allocMonoTheory.release_dead_spills_next_offset,
       allocMonoTheory.release_dead_spills_spill_base] >>
  simp[stackPlanOpsTheory.release_dead_spills_def] >>
  qmatch_goalsub_abbrev_tac `FOLDL f s xs` >>
  `!ys ps. (FOLDL f ps ys).ps_label_counter = ps.ps_label_counter` by
    (Induct >> simp[Abbr `f`] >> rpt gen_tac >>
     Cases_on `h` >> simp[]) >>
  simp[Abbr `s`]
QED

Theorem splice_two_y_return:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops r. generate_fn_plan_aux (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    ["Y"] ["H";"E"] q = SOME (ops,["Y";"H";"E"],r) /\
    r.ps_alloc.sa_next_offset = 608 /\ r.ps_alloc.sa_spill_base = 0 /\ r.ps_label_counter = 0
Proof
  gen_tac >> strip_tac >> drule splice_two_y_block >> strip_tac >>
  qpat_x_assum `q = _` kall_tac >>
  gvs[splice_two_y_data] >>
  simp[Once generate_fn_plan_aux_def, splice_two_y_data] >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[Once generate_fn_plan_aux_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem splice_two_dfs_b:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  dfs_aux_call (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0)
    ["B"] ["Y";"H";"E"] q
Proof
  gen_tac >> strip_tac >> drule splice_two_block_result >> strip_tac >>
  drule splice_two_y_return >> strip_tac >>
  `q.ps_alloc.sa_next_offset = 608 /\ q.ps_alloc.sa_spill_base = 0 /\
   q.ps_label_counter = 0` by (gvs[] >> EVAL_TAC) >>
  qpat_x_assum `q = _` kall_tac >>
  mp_tac splice_two_dfs_h >> strip_tac >>
  mp_tac splice_two_schedule >> strip_tac >>
  drule dfs_aux_call_succs >>
  disch_then (qspec_then `THE (lookup_block "H" splice_two_fn.fn_blocks)` mp_tac) >>
  simp[] >> strip_tac >>
  `q with <|ps_alloc := r.ps_alloc with sa_free_slots := q.ps_alloc.sa_free_slots;
            ps_label_counter := 0|> = q` by
    (simp[stackPlanTypesTheory.plan_state_component_equality,
          stackPlanTypesTheory.spill_alloc_component_equality]) >>
  drule dfs_aux_call_sibling >> simp[] >> strip_tac >>
  drule dfs_aux_call_branch >> simp[]
QED

Theorem splice_two_lineage_b:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  lineage_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0) "B" q
Proof
  gen_tac >> strip_tac >> drule splice_two_dfs_b >> strip_tac >>
  drule splice_two_block_result >> strip_tac >>
  qpat_x_assum `q = _` kall_tac >>
  mp_tac splice_two_lineage_h >> strip_tac >>
  mp_tac splice_two_schedule >> strip_tac >>
  `dfs_block_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0) "B" q` by
    (simp[dfs_block_state_def] >> qexistsl_tac [`[]`,`["Y";"H";"E"]`] >> simp[]) >>
  `dfs_block_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0) "H" splice_loop_e` by
    (simp[dfs_block_state_def] >> qexistsl_tac [`[]`,`["E"]`] >> simp[splice_two_dfs_h]) >>
  `lineage_state (liveness_analyze splice_two_fn) (dfg_build_function splice_two_fn)
    (cfg_analyze splice_two_fn) splice_two_fn (init_cleanup_plan_state NONE [] 0 0) "B"
    (q with <|ps_stack := q.ps_stack; ps_spilled := q.ps_spilled|>)` suffices_by simp[] >>
  irule lineage_state_step >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`NONE`,`F`] >>
  gvs[splice_loop_e_exact]
QED

Theorem splice_two_b_inputs:
  input_vars_from "H"
    (THE (lookup_block "B" splice_two_fn.fn_blocks)).bb_instructions
    (live_vars_at (liveness_analyze splice_two_fn) "B" 0) =
    live_vars_at (liveness_analyze splice_two_fn) "H" 22
Proof
  rewrite_tac[splice_two_h_end_live] >> EVAL_TAC
QED

Theorem splice_two_b_cleanup:
  !q. q.ps_cleanup_height = NONE /\ ~q.ps_cleanup_promised ==>
  clean_stack_plan (liveness_analyze splice_two_fn) (cfg_analyze splice_two_fn)
    splice_two_fn (THE (lookup_block "B" splice_two_fn.fn_blocks)) q = ([],q)
Proof
  rpt strip_tac >>
  `cfg_preds_of (cfg_analyze splice_two_fn) "B" = ["H"]` by EVAL_TAC >>
  `(THE (lookup_block "B" splice_two_fn.fn_blocks)).bb_label = "B"` by EVAL_TAC >>
  `LENGTH (THE (lookup_block "H" splice_two_fn.fn_blocks)).bb_instructions = 22` by EVAL_TAC >>
  simp[clean_stack_plan_def, cleanup_elision_safe_without_height, splice_two_schedule] >>
  once_rewrite_tac[cj 5 splice_two_schedule] >>
  simp[splice_two_b_inputs] >>
  `!xs:string list. FILTER (\v. ~MEM v xs) xs = []` by
    simp[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
  simp[stackPlanOpsTheory.popmany_plan_def]
QED

Theorem splice_two_b_live:
  !k. k < 19 ==>
  live_vars_at (liveness_analyze splice_two_fn) "B" k =
    ["p_r";"p_q";"p_p";"p_o";"p_n";"p_m";"p_l";"p_k";
     "p_j";"p_i";"p_h";"p_g";"p_f";"p_e";"p_d";"p_c";"p_b";"p_a";"cond"] ++
    REVERSE (DROP k ["a";"b";"c";"d";"e";"f";"g";"h";"i";
                    "j";"k";"l";"m";"n";"o";"p";"q";"r"])
Proof
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >>
  CONV_TAC (numLib.BOUNDED_FORALL_CONV EVAL) >> simp[]
QED


Theorem splice_two_b_first_store:
  !q. q = splice_loop_e with <|
      ps_stack := splice_loop_e.ps_stack ++ MAP Var
        ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
      ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
      ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
        TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |> ==>
  ?ops. generate_inst_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn) splice_two_fn
    (mk_inst 43 MSTORE [Lit 0w; Var "a"] [])
    (live_vars_at (liveness_analyze splice_two_fn) "B" 1) F F "B" q =
    SOME (ops,q with ps_stack := splice_loop_e.ps_stack ++ MAP Var
      ["r";"n";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m"])
Proof
  gen_tac >> strip_tac >> gvs[] >> simp[splice_two_b_live] >>
  pure_rewrite_tac[EVAL ``splice_loop_e``] >>
  pure_rewrite_tac[EVAL ``dfg_build_function splice_two_fn``] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``release_dead_spills``, ``liveness_analyze``, ``cfg_analyze``, ``splice_two_fn``]) >>
  dep_rewrite.DEP_REWRITE_TAC[release_dead_spills_live_domain] >>
  conj_tac >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[]
QED
