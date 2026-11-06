Theory fnLineageInvCleanupSpliceProbe
Ancestors fnLineageInvTwoDemandProbe fnLineageInvBoundary fnLineageInvLiteral fnLineageInvSpliceProbe stackPlanGen stackPlanOps

(* Finite cleanup overrides; these abbreviations name only concrete fixtures. *)
Definition cleanup_splice_b_def:
  cleanup_splice_b = splice_loop_e with <|
    ps_stack := splice_loop_e.ps_stack ++ MAP Var
      ["r";"a";"b";"c";"d";"e";"f";"g";"h";"i";"j";"k";"l";"m";"n"];
    ps_spilled := FEMPTY |+ (Var "q",32) |+ (Var "p",64) |+ (Var "o",96);
    ps_alloc := splice_loop_e.ps_alloc with sa_free_slots :=
      TAKE 16 splice_loop_e.ps_alloc.sa_free_slots |>
End

(* All eight requested override choices are covered by these stronger
   concrete setup equations. No dead operands are selected for cleanup. *)
Theorem cleanup_splice_setup_overrides:
  !ch promised.
  clean_stack_plan (liveness_analyze splice_two_fn) (cfg_analyze splice_two_fn)
    splice_two_fn (THE (lookup_block "H" splice_two_fn.fn_blocks))
    (splice_loop_e with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    ([],splice_loop_e with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) /\
  clean_stack_plan (liveness_analyze splice_two_fn) (cfg_analyze splice_two_fn)
    splice_two_fn (THE (lookup_block "B" splice_two_fn.fn_blocks))
    (cleanup_splice_b with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    ([],cleanup_splice_b with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) /\
  clean_stack_plan (liveness_analyze splice_two_fn) (cfg_analyze splice_two_fn)
    splice_two_fn (THE (lookup_block "L" splice_two_fn.fn_blocks))
    (splice_loop_e with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>) =
    ([],splice_loop_e with <|ps_cleanup_height := ch; ps_cleanup_promised := promised|>)
Proof
  rpt gen_tac >> conj_tac >- (EVAL_TAC >> simp[]) >>
  conj_tac >- (EVAL_TAC >> simp[]) >>
  EVAL_TAC >> simp[]
QED

Theorem cleanup_splice_b_marked:
  generated_plan_state_wf_marked 0 cleanup_splice_b
Proof
  EVAL_TAC >>
  pure_rewrite_tac[FORALL_SIMP, AND_CLAUSES] >>
  conj_tac >- (rpt gen_tac >> rpt (IF_CASES_TAC >> gvs[])) >>
  reverse conj_tac >- simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  conj_tac >- (rpt gen_tac >> rpt (IF_CASES_TAC >> gvs[])) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  conj_tac >- (rpt gen_tac >> rpt (IF_CASES_TAC >> gvs[])) >>
  conj_tac
  >- (rewrite_tac[GSYM AND_IMP_INTRO, GSYM RIGHT_FORALL_IMP_THM] >>
      CONV_TAC (BINDER_CONV FORALL_IMP_CONV) >>
      CONV_TAC (TOP_DEPTH_CONV (numLib.BOUNDED_FORALL_CONV ALL_CONV)) >>
      EVAL_TAC >> simp[]) >>
  rpt gen_tac >>
  IF_CASES_TAC >- (rpt strip_tac >> gvs[]) >>
  IF_CASES_TAC >- (rpt strip_tac >> gvs[]) >>
  IF_CASES_TAC >> rpt strip_tac >> gvs[]
QED


Theorem cleanup_splice_first_add_promised:
  generate_inst_plan (liveness_analyze splice_two_fn)
    (dfg_build_function splice_two_fn) (cfg_analyze splice_two_fn)
    splice_two_fn (mk_inst 21 ADD [Lit 1w; Lit 2w] ["t"])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 1) F F "H"
    (splice_loop_e with <|ps_cleanup_height := NONE; ps_cleanup_promised := T|>) =
  SOME ([SOPush (Lit 2w); SOPush (Lit 1w); SOEmit "ADD"],
    splice_loop_e with <|ps_stack := splice_loop_e.ps_stack ++ [Var "t"];
      ps_cleanup_height := NONE; ps_cleanup_promised := T|>)
Proof
  qmatch_goalsub_abbrev_tac `generate_inst_plan _ _ _ _ _ _ _ _ _ ps` >>
  mp_tac splice_two_live_observe >> simp[] >> strip_tac >>
  `optimistic_swap_plan (dfg_build_function splice_two_fn)
    (mk_inst 21 ADD [Lit 1w; Lit 2w] ["t"])
    (live_vars_at (liveness_analyze splice_two_fn) "H" 1) F
    (ps with ps_stack := ps.ps_stack ++ [Var "t"]) =
    ([],ps with ps_stack := ps.ps_stack ++ [Var "t"])` by
    (simp[Abbr `ps`] >>
     asm_rewrite_tac[splice_loop_e_exact, optimistic_swap_plan_def,
       venomInstTheory.mk_inst_def] >> EVAL_TAC) >>
  `MEM "t" (live_vars_at (liveness_analyze splice_two_fn) "H" 1)` by simp[] >>
  drule_all literal_add_inst_plan >>
  simp[release_dead_spills_def, Abbr `ps`, splice_loop_e_exact] >>
  strip_tac >> first_x_assum irule
QED
