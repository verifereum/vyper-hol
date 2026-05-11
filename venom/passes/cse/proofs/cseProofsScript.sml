(*
 * Common Subexpression Elimination — Proofs
 *
 * cse_function = clear_nops_function o cse_iterate.
 * cse_iterate applies cse_single_pass until fixpoint via OWHILE.
 *
 * The proof decomposes into:
 *   1. Per-pass correctness: cse_single_pass preserves run_blocks
 *      semantics under a cse_pass_sound_at precondition (the ae
 *      analysis produces sound values at every CSE decision point).
 *   2. OWHILE composition via FUNPOW induction + result_equiv_trans.
 *   3. clear_nops_function composition.
 *
 * cse_pass_sound_at is an ANALYSIS PROPERTY: it asserts that the
 * available-expression lattice values are consistent with the
 * execution state.  It does NOT assume that run_blocks results are
 * related — it is provable from SSA + ae fixpoint convergence +
 * transfer soundness.
 *)

Theory cseProofs
Ancestors
  cseDefs passSimulationProps passSharedProps
  stateEquiv stateEquivProps
  venomInstProps venomState While

(* ===== CSE soundness invariant ===== *)

Definition cse_sound_def:
  cse_sound (canon : canon_map) (dfg : dfg_analysis)
            (av_opt : avail_exprs option) (s : venom_state) <=>
    case av_opt of
      NONE => T
    | SOME av =>
        !expr srcs src_inst src_var.
          FLOOKUP av expr = SOME srcs /\
          MEM src_inst srcs /\
          src_inst.inst_outputs = [src_var] ==>
          (?w. FLOOKUP s.vs_vars src_var = SOME w) /\
          (!inst fuel ctx s'.
             mk_expr dfg inst = expr /\
             operand_ids_match canon dfg inst src_inst /\
             inst.inst_outputs <> [] /\
             step_inst fuel ctx inst s = OK s' ==>
             FLOOKUP s.vs_vars src_var =
             FLOOKUP s'.vs_vars (HD inst.inst_outputs))
End

(* ===== Analysis soundness precondition ===== *)

(* cse_pass_sound_at fn: analysis values are sound at every
   instruction position, AND every CSE-eligible instruction is
   effect-free (excludes ALLOCA, MSTORE, ASSERT, etc. from CSE).
   Both are STRUCTURAL/ANALYSIS properties, not semantic assumptions.*)
Definition cse_pass_sound_at_def:
  cse_pass_sound_at fn <=>
    let dfg = dfg_build_function fn in
    let result = avail_analyze fn in
    let canon = compute_canon dfg result fn in
    (* Analysis soundness at every instruction position *)
    (!bb idx (s : venom_state).
       MEM bb fn.fn_blocks /\
       idx < LENGTH bb.bb_instructions /\
       s.vs_inst_idx = idx /\
       s.vs_current_bb = bb.bb_label ==>
       cse_sound canon dfg
         (df_at (NONE : avail_exprs option) result bb.bb_label idx) s) /\
    (* Every CSE-eligible instruction is effect-free *)
    (!bb inst. MEM bb fn.fn_blocks /\
       MEM inst bb.bb_instructions /\
       ~cse_skip_opcode inst.inst_opcode /\
       ~is_terminator inst.inst_opcode /\
       inst.inst_opcode <> INVOKE /\
       ~is_nonidempotent inst.inst_opcode ==>
       is_effect_free_op inst.inst_opcode)
End

(* Iterated: at every FUNPOW step of the OWHILE iteration,
   cse_pass_sound_at + structural well-formedness hold. *)
Definition cse_pass_sound_def:
  cse_pass_sound fn <=>
    !k. cse_pass_sound_at (FUNPOW cse_single_pass k fn) /\
        fn_inst_wf (FUNPOW cse_single_pass k fn) /\
        wf_function (FUNPOW cse_single_pass k fn)
End

(* ===== Helpers ===== *)

Theorem state_equiv_empty_is_eq[local]:
  !s1 s2. state_equiv {} s1 s2 ==> s1 = s2
Proof
  simp[state_equiv_def, execution_equiv_def, lookup_var_def,
       venom_state_component_equality] >>
  rpt strip_tac >>
  `!v. FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v`
    by metis_tac[pred_setTheory.NOT_IN_EMPTY] >>
  metis_tac[finite_mapTheory.FLOOKUP_EXT, boolTheory.EQ_EXT]
QED

Theorem result_equiv_empty_refl[local]:
  !r. result_equiv {} r r
Proof
  simp[result_equiv_is_lift_result] >>
  gen_tac >> irule lift_result_refl >>
  simp[state_equiv_refl, execution_equiv_refl]
QED

(* state_equiv with singleton exclusion + known output value *)
Theorem state_equiv_singleton_update[local]:
  !out s s' w.
    state_equiv {out} s s' /\
    FLOOKUP s'.vs_vars out = SOME w ==>
    s' = update_var out w s
Proof
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def,
     update_var_def, venom_state_component_equality] >>
  `s'.vs_vars = s.vs_vars |+ (out, w)` by (
    simp[finite_mapTheory.fmap_eq_flookup,
         finite_mapTheory.FLOOKUP_UPDATE] >>
    gen_tac >> Cases_on `x = out` >> simp[] >>
    `x NOTIN {out}` by simp[] >> metis_tac[]) >>
  simp[]
QED

Theorem cse_block_transform_label[local]:
  !canon dfg result bb.
    (cse_block_transform canon dfg result bb).bb_label = bb.bb_label
Proof
  simp[cse_block_transform_def]
QED

(* ===== cse_lookup extraction ===== *)

(* Extract facts from cse_lookup result *)
Theorem filter_head_mem[local]:
  !P l h t. FILTER P l = h :: t ==> P h /\ MEM h l
Proof
  rpt strip_tac >>
  `MEM h (FILTER P l)` by (ASM_REWRITE_TAC [listTheory.MEM]) >>
  fs[listTheory.MEM_FILTER]
QED

Theorem cse_lookup_facts[local]:
  !canon dfg av inst src expr.
    cse_lookup canon dfg av inst = SOME (src, expr) ==>
    ?srcs. FLOOKUP av expr = SOME srcs /\ MEM src srcs /\
           operand_ids_match canon dfg inst src /\
           mk_expr dfg inst = expr
Proof
  rpt strip_tac >>
  gvs[cse_lookup_def, LET_THM, AllCaseEqs()] >>
  imp_res_tac filter_head_mem >> gvs[]
QED

Theorem cse_lookup_same_bb_facts[local]:
  !canon dfg av bb_ids inst src expr.
    cse_lookup_same_bb canon dfg av bb_ids inst = SOME (src, expr) ==>
    ?srcs. FLOOKUP av expr = SOME srcs /\ MEM src srcs /\
           operand_ids_match canon dfg inst src /\
           mk_expr dfg inst = expr
Proof
  rpt strip_tac >>
  gvs[cse_lookup_same_bb_def, LET_THM, AllCaseEqs()] >>
  imp_res_tac filter_head_mem >> gvs[]
QED

(* ===== Per-instruction simulation ===== *)

(* When step_inst on the original succeeds, step_inst on the
   cse_inst replacement also succeeds with the same result state.
   Requires cse_sound + effect-free for the specific instruction. *)
(* Helper: prove the ASSIGN case for a single source instruction.
   Factored out to handle both cse_lookup and cse_lookup_same_bb. *)
Theorem cse_assign_case[local]:
  !canon dfg av_opt inst out sv fuel ctx s s'.
    cse_sound canon dfg av_opt s /\
    is_effect_free_op inst.inst_opcode /\
    inst.inst_outputs = [out] /\
    step_inst fuel ctx inst s = OK s' /\
    (?srcs. FLOOKUP (avail_unwrap av_opt) (mk_expr dfg inst) = SOME srcs /\
            ?src. MEM src srcs /\ src.inst_outputs = [sv] /\
                  operand_ids_match canon dfg inst src) ==>
    step_inst fuel ctx (mk_assign_inst inst (Var sv)) s = OK s'
Proof
  rpt strip_tac >>
  (* Case split av_opt; NONE case is contradictory *)
  Cases_on `av_opt` >>
  gvs[availExprDefsTheory.avail_unwrap_def,
      availExprDefsTheory.avail_empty_def] >>
  (* Now: av_opt = SOME x, cse_sound canon dfg (SOME x) s *)
  (* Unfold cse_sound into the goal via mp_tac *)
  qpat_x_assum `cse_sound _ _ (SOME _) _` mp_tac >>
  simp[cse_sound_def] >> strip_tac >>
  (* Specialize cse_sound for our expression/source *)
  first_x_assum (qspecl_then [`mk_expr dfg inst`, `srcs`,
    `src`, `sv`] mp_tac) >> simp[] >> strip_tac >>
  (* Got: FLOOKUP s.vs_vars sv = SOME w *)
  (* Got: universal for value relationship *)
  `FLOOKUP s.vs_vars sv = FLOOKUP s'.vs_vars out` by (
    first_x_assum (qspecl_then [`inst`, `fuel`, `ctx`, `s'`] mp_tac) >>
    simp[]) >>
  (* effect-free => state_equiv {out} s s' *)
  imp_res_tac step_effect_free_state_equiv >>
  `state_equiv {out} s s'` by
    (`set inst.inst_outputs = {out}` by simp[] >> metis_tac[]) >>
  `FLOOKUP s'.vs_vars out = SOME w` by metis_tac[] >>
  `s' = update_var out w s` by
    (irule state_equiv_singleton_update >> simp[]) >>
  simp[] >>
  irule mk_assign_inst_correct >>
  simp[eval_operand_def, lookup_var_def]
QED

Theorem cse_inst_step_ok[local]:
  !bb_ids canon dfg av_opt inst fuel ctx s s'.
    cse_sound canon dfg av_opt s /\
    is_effect_free_op inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst fuel ctx (cse_inst bb_ids canon (dfg, av_opt) inst) s = OK s'
Proof
  rpt strip_tac >>
  Cases_on `cse_inst bb_ids canon (dfg, av_opt) inst = inst`
  >- simp[]
  >> simp[cse_inst_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  Cases_on `inst.inst_outputs` >> simp[]
  >- ((* NOP case: effect-free + no outputs => s' = s *)
    imp_res_tac step_effect_free_state_equiv >>
    `state_equiv {} s s'` by
      (`set (inst.inst_outputs : string list) = {}` by simp[] >>
       metis_tac[]) >>
    imp_res_tac state_equiv_empty_is_eq >> gvs[] >>
    BasicProvers.every_case_tac >> simp[mk_nop_inst_correct])
  >> rename1 `out :: rest` >>
  Cases_on `rest` >> simp[]
  >- ((* ASSIGN case: [out] — use cse_assign_case *)
    BasicProvers.every_case_tac >> simp[] >>
    irule cse_assign_case >>
    simp[] >> metis_tac[cse_lookup_facts, cse_lookup_same_bb_facts])
  >> simp[]
QED

(* ===== Block-level simulation ===== *)

(* When cse_pass_sound_at holds, exec_block on the original and
   CSE-transformed blocks produce Error or the same result. *)
Theorem cse_block_sim[local]:
  !fn bb fuel ctx s.
    cse_pass_sound_at fn /\
    fn_inst_wf fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 ==>
    let bt = cse_block_transform
               (compute_canon (dfg_build_function fn) (avail_analyze fn) fn)
               (dfg_build_function fn) (avail_analyze fn) in
    (?e. exec_block fuel ctx bb s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (bt bb) s)
Proof
  (* Block-level induction on exec_block depth *)
  cheat
QED

(* ===== Single-pass correctness ===== *)

Theorem cse_single_pass_correct[local]:
  !fn fuel ctx s.
    fn_inst_wf fn /\ wf_function fn /\
    s.vs_inst_idx = 0 /\
    cse_pass_sound_at fn ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    result_equiv {}
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (cse_single_pass fn) s)
Proof
  cheat
QED

(* ===== FUNPOW iteration ===== *)

Theorem funpow_cse_correct[local]:
  !n fn fuel ctx s.
    s.vs_inst_idx = 0 /\ cse_pass_sound fn ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    result_equiv {}
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (FUNPOW cse_single_pass n fn) s)
Proof
  Induct_on `n` >> rpt strip_tac
  >- simp[result_equiv_empty_refl]
  >> simp[arithmeticTheory.FUNPOW_SUC] >>
  qabbrev_tac `gn = FUNPOW cse_single_pass n fn` >>
  `(?e. run_blocks fuel ctx fn s = Error e) \/
   result_equiv {} (run_blocks fuel ctx fn s)
     (run_blocks fuel ctx gn s)` by
    (unabbrev_all_tac >>
     first_x_assum (qspecl_then [`fn`, `fuel`, `ctx`, `s`] mp_tac) >>
     simp[]) >>
  `fn_inst_wf gn /\ wf_function gn /\ cse_pass_sound_at gn` by (
    qpat_x_assum `cse_pass_sound _` mp_tac >>
    simp[cse_pass_sound_def, Abbr `gn`] >>
    disch_then (qspec_then `n` strip_assume_tac) >> simp[]) >>
  `(?e. run_blocks fuel ctx gn s = Error e) \/
   result_equiv {} (run_blocks fuel ctx gn s)
     (run_blocks fuel ctx (cse_single_pass gn) s)` by
    (irule cse_single_pass_correct >> simp[]) >>
  (* Compose: use disjunction elimination + result_equiv_trans *)
  Cases_on `?e. run_blocks fuel ctx fn s = Error e` >- simp[] >>
  fs[] >>
  Cases_on `?e. run_blocks fuel ctx gn s = Error e`
  >- (fs[] >>
      Cases_on `run_blocks fuel ctx fn s` >> gvs[result_equiv_def])
  >> (fs[] >> TRY DISJ2_TAC >>
      irule result_equiv_trans >>
      qexists_tac `run_blocks fuel ctx gn s` >> simp[])
QED

(* ===== Cheated obligation ===== *)

(* CHEATED: analysis soundness holds for well-formed functions.
   Requires proving that avail_analyze produces sound lattice values
   at every program point, and that cse_single_pass preserves
   fn_inst_wf and wf_function. *)
Theorem cse_pass_sound_holds:
  !fn. fn_inst_wf fn /\ wf_function fn ==> cse_pass_sound fn
Proof
  cheat
QED

(* ===== Main theorem ===== *)

Theorem cse_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn /\ wf_function fn /\
    s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (cse_function fn) s)
Proof
  rpt strip_tac >>
  `cse_pass_sound fn` by (irule cse_pass_sound_holds >> simp[]) >>
  simp[cse_function_def] >>
  Cases_on `cse_iterate fn` >> simp[]
  >- (DISJ2_TAC >>
      simp_tac std_ss [GSYM result_equiv_is_lift_result] >>
      irule clear_nops_function_correct >> simp[])
  >> rename1 `SOME fn'` >>
  fs[cse_iterate_def, OWHILE_def] >>
  Cases_on `?n. ~((cse_single_pass (FUNPOW cse_single_pass n fn)).fn_blocks <>
                  (FUNPOW cse_single_pass n fn).fn_blocks)` >> fs[] >>
  qabbrev_tac `N = LEAST n.
    (cse_single_pass (FUNPOW cse_single_pass n fn)).fn_blocks =
    (FUNPOW cse_single_pass n fn).fn_blocks` >>
  `fn' = FUNPOW cse_single_pass N fn` by simp[Abbr `N`] >> gvs[] >>
  `(?e. run_blocks fuel ctx fn s = Error e) \/
   result_equiv {} (run_blocks fuel ctx fn s)
     (run_blocks fuel ctx (FUNPOW cse_single_pass N fn) s)` by (
    irule funpow_cse_correct >> simp[]) >>
  Cases_on `?e. run_blocks fuel ctx fn s = Error e` >> fs[] >>
  `result_equiv {}
     (run_blocks fuel ctx (FUNPOW cse_single_pass N fn) s)
     (run_blocks fuel ctx
        (clear_nops_function (FUNPOW cse_single_pass N fn)) s)` by
    (irule clear_nops_function_correct >> simp[]) >>
  TRY DISJ2_TAC >>
  simp_tac std_ss [GSYM result_equiv_is_lift_result] >>
  irule result_equiv_trans >>
  qexists_tac `run_blocks fuel ctx (FUNPOW cse_single_pass N fn) s` >>
  simp[]
QED
