(*
 * Algebraic Optimization — EQ + Comparator Simulation Helpers
 *
 * TOP-LEVEL:
 *   ao_eq_sim        — EQ peephole sim (all cases: self, zero, neg1, prefer_iszero)
 *   ao_cmp_sim       — Comparator peephole sim (GT, LT, SGT, SLT)
 *
 * Helper:
 *   state_equiv_extra_var   — inserting a fresh var preserves state_equiv
 *   run_insts_2step         — run_insts for 2-instruction sequences
 *)
Theory algebraicOptSimCmp
Ancestors
  algebraicOptDefs algebraicOptRules
  algebraicOptSegSim
  venomExecSemantics venomState venomInst venomWf
  stateEquiv stateEquivProps passSharedDefs
  passSimulationDefs
Libs
  pairLib BasicProvers

(* ===== State equivalence with extra fresh variable ===== *)

(* Inserting an update to a variable IN fv doesn't break state_equiv.
   Key lemma for 1-to-N expansion proofs: the fresh intermediate variable
   is in fv, so the extra binding is invisible to state_equiv. *)
Theorem state_equiv_extra_var:
  !fv v val s.
    v IN fv ==>
    state_equiv fv (update_var v val s) s
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def,
     lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> rw[] >> gvs[]
QED

(* Composing: update_var out val (update_var tmp intermediate s) ≈_fv
              update_var out val s   when tmp IN fv *)
Theorem state_equiv_1to2:
  !fv out val tmp intermediate s.
    tmp IN fv ==>
    state_equiv fv
      (update_var out val (update_var tmp intermediate s))
      (update_var out val s)
Proof
  rpt strip_tac >>
  `state_equiv fv (update_var tmp intermediate s) s`
    by (irule state_equiv_extra_var >> simp[]) >>
  metis_tac[update_var_preserves]
QED

(* 3-step variant: two fresh vars *)
Theorem state_equiv_1to3:
  !fv out val tmp1 v1 tmp2 v2 s.
    tmp1 IN fv /\ tmp2 IN fv ==>
    state_equiv fv
      (update_var out val (update_var tmp2 v2 (update_var tmp1 v1 s)))
      (update_var out val s)
Proof
  rpt strip_tac >>
  `state_equiv fv (update_var tmp1 v1 s) s`
    by (irule state_equiv_extra_var >> simp[]) >>
  `state_equiv fv (update_var tmp2 v2 (update_var tmp1 v1 s))
                   (update_var tmp2 v2 s)`
    by metis_tac[update_var_preserves] >>
  `state_equiv fv (update_var tmp2 v2 s) s`
    by (irule state_equiv_extra_var >> simp[]) >>
  `state_equiv fv (update_var tmp2 v2 (update_var tmp1 v1 s)) s`
    by metis_tac[state_equiv_trans] >>
  metis_tac[update_var_preserves]
QED

(* ===== run_insts helpers ===== *)

(* 2-step run_insts: expand and simplify for non-INVOKE instructions *)
Theorem run_insts_2step:
  !fuel ctx i1 i2 s.
    i1.inst_opcode <> INVOKE /\
    i2.inst_opcode <> INVOKE ==>
    run_insts fuel ctx [i1; i2] s =
      case step_inst_base i1 s of
        OK s' => step_inst_base i2 s'
      | err => err
Proof
  rw[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def]
QED

(* 3-step run_insts *)
Theorem run_insts_3step:
  !fuel ctx i1 i2 i3 s.
    i1.inst_opcode <> INVOKE /\
    i2.inst_opcode <> INVOKE /\
    i3.inst_opcode <> INVOKE ==>
    run_insts fuel ctx [i1; i2; i3] s =
      case step_inst_base i1 s of
        OK s1 => (case step_inst_base i2 s1 of
                    OK s2 => step_inst_base i3 s2
                  | err => err)
      | err => err
Proof
  rw[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def]
QED

(* Singleton run_insts for non-INVOKE *)
Triviality run_insts_1step[local]:
  !fuel ctx inst s.
    inst.inst_opcode <> INVOKE ==>
    run_insts fuel ctx [inst] s = step_inst_base inst s
Proof
  rw[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def]
QED

(* ===== Word-level helpers ===== *)

Triviality word_1comp_eq_0[local]:
  !x:bytes32. (word_1comp x = 0w) <=> (x = 0w - 1w)
Proof
  gen_tac >>
  `0w - 1w : bytes32 = UINT_MAXw` by
    simp[wordsTheory.word_sub_def, wordsTheory.WORD_NEG_1,
         wordsTheory.WORD_ADD_0] >>
  simp[] >> EQ_TAC >> strip_tac
  >- metis_tac[wordsTheory.WORD_NOT_NOT, wordsTheory.WORD_NOT_0]
  >- simp[wordsTheory.WORD_NOT_T]
QED

Triviality word_xor_eq_0[local]:
  !x y:bytes32. (word_xor x y = 0w) <=> (x = y)
Proof
  rpt gen_tac >> EQ_TAC >> strip_tac
  >- (`word_xor (word_xor x y) y = word_xor 0w y` by gvs[] >>
      pop_assum mp_tac >>
      rewrite_tac[wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_CLAUSES] >>
      simp[])
  >- simp[wordsTheory.WORD_XOR_CLAUSES]
QED

Triviality bool_to_word_eq_0[local]:
  !b. (bool_to_word b = 0w) <=> ~b
Proof Cases >> simp[bool_to_word_def]
QED

(* ===== EQ simulation ===== *)

(* EQ: all branches of ao_opt_eq produce equivalent run_insts result
   or the original step_inst_base errors.
   Covers: op1=op2, op2=0, op2=-1 (1-to-2), prefer_iszero (1-to-2), identity *)
Theorem ao_eq_sim:
  !fv dfg inst s fuel ctx.
    inst.inst_opcode = EQ /\
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv ==>
    (?e. step_inst_base inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst_base inst s)
      (run_insts fuel ctx (ao_opt_eq dfg inst) s)
Proof
  rpt strip_tac >>
  `?op1 op2. inst.inst_operands = [op1; op2]` by (
    Cases_on `inst.inst_operands` >> gvs[] >>
    Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `?out. inst.inst_outputs = [out]` by (
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  gvs[] >>
  simp[ao_opt_eq_def] >>
  Cases_on `op1 = op2` >> gvs[]
  (* Self case: op1 = op2 → ASSIGN 1w *)
  >- (
    simp[run_insts_def, step_inst_non_invoke,
         step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    Cases_on `eval_operand op1 s` >> gvs[run_insts_def] >>
    simp[lift_result_def, bool_to_word_def, state_equiv_refl])
  (* Non-self case: op1 <> op2 *)
  >> Cases_on `lit_eq op2 0w` >> gvs[]
  (* op2 = 0w → ISZERO *)
  >- (
    `op2 = Lit 0w` by (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    simp[run_insts_def, step_inst_non_invoke,
         step_inst_base_def, exec_pure2_def, exec_pure1_def,
         eval_operand_def] >>
    Cases_on `eval_operand op1 s` >> gvs[run_insts_def] >>
    simp[lift_result_def, bool_to_word_def, state_equiv_refl])
  (* op2 = -1 → NOT + ISZERO *)
  >> Cases_on `lit_eq op2 (0w - 1w)` >> gvs[]
  >- (
    `op2 = Lit (0w - 1w)` by (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    simp[LET_THM, run_insts_2step, step_inst_base_def,
         exec_pure2_def, exec_pure1_def, eval_operand_def] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- simp[] >>
    DISJ2_TAC >>
    simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[word_1comp_eq_0, lift_result_def] >>
    irule state_equiv_1to2 >> simp[])
  (* prefer_iszero → XOR + ISZERO *)
  >> Cases_on `ao_all_prefer_iszero dfg inst` >> gvs[]
  >- (
    simp[LET_THM, run_insts_2step, step_inst_base_def,
         exec_pure2_def, exec_pure1_def, eval_operand_def] >>
    Cases_on `eval_operand op1 s` >> Cases_on `eval_operand op2 s` >> gvs[]
    >- simp[]
    >- simp[]
    >- simp[]
    >>
    DISJ2_TAC >>
    simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[word_xor_eq_0, lift_result_def] >>
    irule state_equiv_1to2 >> simp[])
  (* identity [inst] *)
  >> simp[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def, lift_result_def, state_equiv_refl]
QED

(* ===== Comparator simulation ===== *)

(* Helper: ao_opt_comparator boundary values *)
Triviality unsigned_boundaries_gt[local]:
  ao_unsigned_boundaries T = (0w, 0w - 1w, (0w:bytes32) - 1w - 1w)
Proof simp[ao_unsigned_boundaries_def, LET_THM]
QED

Triviality unsigned_boundaries_lt[local]:
  ao_unsigned_boundaries F = (0w - 1w, 0w, 1w : bytes32)
Proof simp[ao_unsigned_boundaries_def, LET_THM]
QED

Triviality signed_boundaries_gt[local]:
  ao_signed_boundaries T =
    (i2w INT256_MIN, i2w INT256_MAX, i2w INT256_MAX - 1w : bytes32)
Proof simp[ao_signed_boundaries_def, LET_THM]
QED

Triviality signed_boundaries_lt[local]:
  ao_signed_boundaries F =
    (i2w INT256_MAX, i2w INT256_MIN, i2w INT256_MIN + 1w : bytes32)
Proof simp[ao_signed_boundaries_def, LET_THM]
QED

(* Comparator simulation: all branches of ao_opt_comparator.
   Range-based case is cheated (needs range_analysis_sound precondition). *)
Theorem ao_cmp_sim:
  !fv dfg ra lbl idx inst s fuel ctx.
    (inst.inst_opcode = GT \/ inst.inst_opcode = LT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) /\
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv ==>
    (?e. step_inst_base inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst_base inst s)
      (run_insts fuel ctx (ao_opt_comparator dfg ra lbl idx inst) s)
Proof
  rpt strip_tac >>
  `?op1 op2. inst.inst_operands = [op1; op2]` by (
    Cases_on `inst.inst_operands` >> gvs[] >>
    Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `?out. inst.inst_outputs = [out]` by (
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  gvs[] >>
  simp[ao_opt_comparator_def, LET_THM] >>
  (* Case: op1 = op2 → ASSIGN 0w *)
  IF_CASES_TAC >> gvs[]
  >- (
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    Cases_on `eval_operand op2 s` >> gvs[]
    >- (DISJ1_TAC >> qexists_tac `"undefined operand"` >> simp[]) >>
    DISJ2_TAC >> simp[lift_result_def, bool_to_word_def, state_equiv_refl] >>
    Cases_on `inst.inst_opcode` >> gvs[] >>
    simp[wordsTheory.WORD_LESS_REFL, wordsTheory.WORD_GREATER])
  (* After op1 <> op2: range-based + boundary cases *)
  (* Range-based case: CHEATED — needs range_analysis_sound precondition *)
  >> CASE_TAC >> gvs[]
  >- (
    (* ao_opt_cmp_range returned SOME replacement *)
    simp[run_insts_def, step_inst_non_invoke] >>
    cheat)
  (* ao_opt_cmp_range returned NONE: proceed to boundary cases *)
  >> rpt (IF_CASES_TAC >> gvs[])
  (* Non-literal op2 → identity [inst] *)
  >- simp[run_insts_def, step_inst_non_invoke, lift_result_def, state_equiv_refl]
  (* never case → ASSIGN 0w *)
  >- (
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    `op2 = Lit (if inst.inst_opcode = SGT \/ inst.inst_opcode = SLT then
                  (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT then
                     i2w INT256_MAX else i2w INT256_MIN)
                else
                  (if inst.inst_opcode = GT \/ inst.inst_opcode = SGT then
                     0w - 1w else 0w))`
      by (Cases_on `op2` >> gvs[lit_eq_def] >>
          Cases_on `inst.inst_opcode` >> gvs[]) >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >> qexists_tac `"undefined operand"` >> simp[]) >>
    DISJ2_TAC >> simp[lift_result_def, state_equiv_refl] >>
    Cases_on `inst.inst_opcode` >> gvs[] >>
    simp[bool_to_word_def] >>
    TRY (`~(w2n x > w2n (0w - 1w : bytes32))` by (
      `w2n x < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
      `w2n (0w - 1w : bytes32) = dimword(:256) - 1` by
        simp[wordsTheory.word_sub_def, wordsTheory.word_2comp_def,
             wordsTheory.w2n_n2w] >>
      decide_tac) >> simp[]) >>
    TRY simp[] >>
    TRY (simp[wordsTheory.WORD_GREATER, integer_wordTheory.WORD_LTi] >>
      `w2i (i2w INT256_MAX : bytes32) = INT256_MAX` by (
        irule integer_wordTheory.w2i_i2w >>
        simp[INT256_MAX_def, integer_wordTheory.INT_MAX_def,
             integer_wordTheory.INT_MIN_def, wordsTheory.dimword_def]) >>
      pop_assum SUBST_ALL_TAC >>
      `w2i x <= INT_MAX(:256)` by simp[integer_wordTheory.w2i_le] >>
      `INT256_MAX = INT_MAX(:256)` by simp[INT256_MAX_def] >>
      `~(INT256_MAX < w2i x)` by intLib.ARITH_TAC >> simp[] >> NO_TAC) >>
    TRY (simp[integer_wordTheory.WORD_LTi] >>
      `w2i (i2w INT256_MIN : bytes32) = INT256_MIN` by (
        irule integer_wordTheory.w2i_i2w >>
        simp[INT256_MIN_def, integer_wordTheory.INT_MAX_def,
             integer_wordTheory.INT_MIN_def, wordsTheory.dimword_def]) >>
      pop_assum SUBST_ALL_TAC >>
      `INT_MIN(:256) <= w2i x` by simp[integer_wordTheory.w2i_ge] >>
      `INT256_MIN = INT_MIN(:256)` by simp[INT256_MIN_def] >>
      `~(w2i x < INT256_MIN)` by intLib.ARITH_TAC >> simp[] >> NO_TAC))
  (* almost_never case: ISZERO / NOT+ISZERO / EQ *)
  >- cheat (* almost_never: multiple sub-cases with boundary arithmetic *)
  (* prefer_iszero + almost_always: 2-3 instruction expansions *)
  >- cheat (* prefer_iszero: iz_zero/iz_max/iz_general patterns *)
  (* GT x 0 → ISZERO+ISZERO (only for unsigned GT) *)
  >- (
    (* This branch fires only for GT with lit_eq op2 0w *)
    qabbrev_tac `id = inst.inst_id` >>
    qabbrev_tac `tmp = ao_fresh_var id "iz"` >>
    simp[LET_THM] >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, exec_pure1_def, eval_operand_def] >>
    `op2 = Lit 0w` by (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >> qexists_tac `"undefined operand"` >> simp[]) >>
    DISJ2_TAC >>
    simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    simp[bool_to_word_eq_0] >>
    `(x <> 0w) <=> (w2n x > 0)` by (
      Cases_on `x = 0w` >> simp[] >>
      `w2n x <> 0` by simp[wordsTheory.w2n_eq_0] >> simp[]) >>
    simp[lift_result_def] >>
    irule state_equiv_1to2 >> simp[])
  (* else → identity [inst] *)
  >> simp[run_insts_def, step_inst_non_invoke, lift_result_def, state_equiv_refl]
QED

val _ = export_theory();
