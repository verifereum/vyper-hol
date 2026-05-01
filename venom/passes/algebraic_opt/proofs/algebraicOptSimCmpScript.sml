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
  algebraicOptSegSim valueRangeDefs
  venomExecSemantics venomState venomInst venomWf
  stateEquiv stateEquivProps passSharedDefs
  passSimulationDefs
Libs
  pairLib BasicProvers intLib wordsLib

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

(* Composing: update_var out val s ≈_fv
              update_var out val (update_var tmp intermediate s)
   when tmp IN fv.  Direction matches lift_result: original first. *)
Theorem state_equiv_1to2:
  !fv out val tmp intermediate s.
    tmp IN fv ==>
    state_equiv fv
      (update_var out val s)
      (update_var out val (update_var tmp intermediate s))
Proof
  rpt strip_tac >>
  `state_equiv fv s (update_var tmp intermediate s)`
    by (irule state_equiv_sym >> irule state_equiv_extra_var >> simp[]) >>
  metis_tac[update_var_preserves]
QED

(* 3-step variant: two fresh vars *)
Theorem state_equiv_1to3:
  !fv out val tmp1 v1 tmp2 v2 s.
    tmp1 IN fv /\ tmp2 IN fv ==>
    state_equiv fv
      (update_var out val s)
      (update_var out val (update_var tmp2 v2 (update_var tmp1 v1 s)))
Proof
  rpt strip_tac >>
  `state_equiv fv s (update_var tmp1 v1 s)`
    by (irule state_equiv_sym >> irule state_equiv_extra_var >> simp[]) >>
  `state_equiv fv (update_var tmp2 v2 s)
                   (update_var tmp2 v2 (update_var tmp1 v1 s))`
    by metis_tac[update_var_preserves] >>
  `state_equiv fv s (update_var tmp2 v2 s)`
    by (irule state_equiv_sym >> irule state_equiv_extra_var >> simp[]) >>
  `state_equiv fv s (update_var tmp2 v2 (update_var tmp1 v1 s))`
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

(* lookup_var / eval_operand through update_var *)
Triviality lookup_var_update[local]:
  !x v s y. lookup_var y (update_var x v s) =
    if x = y then SOME v else lookup_var y s
Proof
  simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Triviality eval_operand_update_same[local]:
  !v val s. eval_operand (Var v) (update_var v val s) = SOME val
Proof
  simp[eval_operand_def, lookup_var_update]
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
    simp[LET_THM] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >> simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    rename1 `eval_operand op1 s = SOME v1` >>
    DISJ2_TAC >>
    (* Original: EQ(op1, -1) → update_var out (bool_to_word (v1 = 0w-1w)) s *)
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    (* Replacement: run_insts [NOT, ISZERO] *)
    qabbrev_tac `tmp = ao_fresh_var inst.inst_id "not"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, word_1comp_eq_0, lift_result_def] >>
    irule state_equiv_1to2 >> simp[])
  (* prefer_iszero → XOR + ISZERO *)
  >> Cases_on `ao_all_prefer_iszero dfg inst` >> gvs[]
  >- (
    simp[LET_THM] >>
    Cases_on `eval_operand op1 s` >> Cases_on `eval_operand op2 s` >> gvs[]
    >- (DISJ1_TAC >> simp[step_inst_base_def, exec_pure2_def, eval_operand_def])
    >- (DISJ1_TAC >> simp[step_inst_base_def, exec_pure2_def, eval_operand_def])
    >- (DISJ1_TAC >> simp[step_inst_base_def, exec_pure2_def, eval_operand_def])
    >>
    rename1 `eval_operand op1 s = SOME v1` >>
    rename1 `eval_operand op2 s = SOME v2` >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    qabbrev_tac `tmp = ao_fresh_var inst.inst_id "xor"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, word_xor_eq_0, lift_result_def] >>
    irule state_equiv_1to2 >> simp[])
  (* identity [inst] *)
  >> simp[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def, lift_result_def,
                   state_equiv_refl, execution_equiv_refl]
QED

(* ===== Comparator simulation ===== *)

(* ===== Word arithmetic for comparator boundaries ===== *)

(* Unsigned: nothing is > UINT_MAX *)
Triviality gt_never[local]:
  !x:bytes32. ~(w2n x > w2n (0w - 1w : bytes32))
Proof
  gen_tac >>
  `w2n x < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
  `w2n (0w - 1w : bytes32) = dimword(:256) - 1` suffices_by DECIDE_TAC >>
  simp[wordsTheory.word_sub_def, wordsTheory.WORD_ADD_0,
       wordsTheory.WORD_NEG_1, wordsTheory.word_T_def,
       wordsTheory.UINT_MAX_def]
QED

(* Unsigned: nothing is < 0 *)
Triviality lt_never[local]:
  !x:bytes32. ~(w2n x < w2n (0w : bytes32))
Proof simp[]
QED

(* GT x 0 iff x <> 0 *)
Triviality gt_zero[local]:
  !x:bytes32. (w2n x > 0) <=> (x <> 0w)
Proof
  gen_tac >> EQ_TAC >> strip_tac
  >- (CCONTR_TAC >> gvs[])
  >- (`w2n x <> 0` suffices_by DECIDE_TAC >>
      strip_tac >> gvs[] >>
      `x = n2w (w2n x)` by simp[wordsTheory.n2w_w2n] >> gvs[])
QED

val word_sub_simp = [wordsTheory.word_sub_def, wordsTheory.WORD_ADD_0,
  wordsTheory.WORD_NEG_1, wordsTheory.word_T_def, wordsTheory.UINT_MAX_def];

(* LT x UINT_MAX iff x <> UINT_MAX *)
Triviality lt_max[local]:
  !x:bytes32. (w2n x < w2n (0w - 1w : bytes32)) <=> (x <> 0w - 1w)
Proof
  gen_tac >>
  `w2n (0w - 1w : bytes32) = dimword(:256) - 1` by simp word_sub_simp >>
  `w2n x < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
  Cases_on `x = 0w - 1w` >> gvs[] >>
  `w2n x <> dimword(:256) - 1` suffices_by DECIDE_TAC >>
  strip_tac >> fs[] >>
  metis_tac[wordsTheory.w2n_11]
QED

(* GT x (UINT_MAX - 1) iff x = UINT_MAX *)
Triviality gt_almost_never[local]:
  !x:bytes32. (w2n x > w2n (0w - 1w - 1w : bytes32)) <=> (x = 0w - 1w)
Proof
  gen_tac >>
  mp_tac (Q.SPEC `0w - 1w`
    (INST_TYPE [alpha |-> ``:256``] wordsTheory.SUC_WORD_PRED)) >>
  simp[wordsTheory.word_sub_def, wordsTheory.WORD_ADD_0,
       wordsTheory.word_T_not_zero] >>
  strip_tac >>
  `w2n (-1w : bytes32) = dimword(:256) - 1` by simp word_sub_simp >>
  `w2n x < dimword(:256)` by simp[wordsTheory.w2n_lt] >>
  EQ_TAC >> strip_tac
  >- (`w2n x = w2n (-1w : bytes32)` by DECIDE_TAC >>
      fs[wordsTheory.w2n_11])
  >- (gvs[] >> DECIDE_TAC)
QED

(* LT x 1 iff x = 0 *)
Triviality lt_almost_never[local]:
  !x:bytes32. (w2n x < w2n (1w : bytes32)) <=> (x = 0w)
Proof
  gen_tac >> simp[] >>
  EQ_TAC >> strip_tac >> gvs[] >>
  `w2n x = 0` by DECIDE_TAC >>
  `x = n2w (w2n x)` by simp[wordsTheory.n2w_w2n] >> gvs[]
QED

(* Helper: INT_MIN <= INT_MAX for 256-bit words *)
Triviality int_min_le_max_256[local]:
  INT_MIN (:256) <= INT_MAX (:256)
Proof
  mp_tac (INST_TYPE [alpha |-> ``:256``]
          integer_wordTheory.INT_ZERO_LT_INT_MIN) >>
  rewrite_tac[integer_wordTheory.INT_MIN_def] >> intLib.ARITH_TAC
QED

(* Signed: nothing is > INT_MAX *)
Triviality sgt_never[local]:
  !x:bytes32. ~word_gt x (i2w INT256_MAX)
Proof
  gen_tac >> rewrite_tac[integer_wordTheory.WORD_GTi, INT256_MAX_def] >>
  `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by (
    irule integer_wordTheory.w2i_i2w >>
    mp_tac (INST_TYPE [alpha |-> ``:256``]
            integer_wordTheory.INT_ZERO_LT_INT_MIN) >>
    rewrite_tac[integer_wordTheory.INT_MIN_def] >> intLib.ARITH_TAC) >>
  pop_assum SUBST_ALL_TAC >>
  mp_tac (Q.SPEC `x` (INST_TYPE [alpha |-> ``:256``]
          integer_wordTheory.w2i_le)) >>
  intLib.ARITH_TAC
QED

(* Signed: nothing is < INT_MIN *)
Triviality slt_never[local]:
  !x:bytes32. ~word_lt x (i2w INT256_MIN)
Proof
  gen_tac >> rewrite_tac[integer_wordTheory.WORD_LTi, INT256_MIN_def] >>
  `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by (
    irule integer_wordTheory.w2i_i2w >>
    mp_tac (INST_TYPE [alpha |-> ``:256``]
            integer_wordTheory.INT_ZERO_LT_INT_MIN) >>
    rewrite_tac[integer_wordTheory.INT_MIN_def] >> intLib.ARITH_TAC) >>
  pop_assum SUBST_ALL_TAC >>
  mp_tac (Q.SPEC `x` (INST_TYPE [alpha |-> ``:256``]
          integer_wordTheory.w2i_ge)) >>
  intLib.ARITH_TAC
QED

(* Comparator self-comparison: cmp x x = F for all comparators *)
Triviality cmp_self_false[local]:
  (!x:bytes32. ~(w2n x > w2n x)) /\
  (!x:bytes32. ~(w2n x < w2n x)) /\
  (!x:bytes32. ~word_gt x x) /\
  (!x:bytes32. ~word_lt x x)
Proof
  simp[wordsTheory.WORD_LESS_REFL, wordsTheory.WORD_GREATER]
QED

(* ===== Signed boundary non-zero facts ===== *)

(* Tactic: prove w2i(i2w X) = X for signed 256-bit constants *)
val w2i_i2w_tac =
  irule integer_wordTheory.w2i_i2w >>
  rewrite_tac[integer_wordTheory.INT_MAX_def, integer_wordTheory.INT_MIN_def,
              wordsTheory.INT_MIN_def] >>
  `dimindex(:256) = 256` by
    (ACCEPT_TAC (wordsLib.SIZES_CONV ``dimindex(:256)``)) >>
  gvs[] >> EVAL_TAC;

(* i2w INT256_MAX <> 0w *)
Triviality sgt_never_ne_0[local]:
  i2w INT256_MAX <> (0w : bytes32)
Proof
  strip_tac >>
  `w2i (i2w INT256_MAX : bytes32) = w2i (0w : bytes32)` by gvs[] >>
  pop_assum mp_tac >>
  rewrite_tac[integer_wordTheory.word_0_w2i, INT256_MAX_def] >>
  `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  rewrite_tac[integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def] >>
  `dimindex(:256) = 256` by
    (ACCEPT_TAC (wordsLib.SIZES_CONV ``dimindex(:256)``)) >>
  gvs[] >> EVAL_TAC
QED

(* i2w INT256_MAX <> 0w - 1w *)
Triviality sgt_never_ne_max[local]:
  i2w INT256_MAX <> (0w - 1w : bytes32)
Proof
  rewrite_tac[wordsTheory.word_sub_def, wordsTheory.WORD_ADD_0] >>
  strip_tac >>
  `w2i (i2w INT256_MAX : bytes32) = w2i (-1w : bytes32)` by gvs[] >>
  pop_assum mp_tac >>
  rewrite_tac[integer_wordTheory.w2i_minus_1, INT256_MAX_def] >>
  `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  rewrite_tac[integer_wordTheory.INT_MAX_def, wordsTheory.INT_MIN_def] >>
  `dimindex(:256) = 256` by
    (ACCEPT_TAC (wordsLib.SIZES_CONV ``dimindex(:256)``)) >>
  gvs[] >> EVAL_TAC
QED

(* i2w INT256_MIN <> 0w *)
Triviality slt_never_ne_0[local]:
  i2w INT256_MIN <> (0w : bytes32)
Proof
  strip_tac >>
  `w2i (i2w INT256_MIN : bytes32) = w2i (0w : bytes32)` by gvs[] >>
  pop_assum mp_tac >>
  rewrite_tac[integer_wordTheory.word_0_w2i, INT256_MIN_def] >>
  `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``]
          integer_wordTheory.INT_ZERO_LT_INT_MIN) >>
  intLib.ARITH_TAC
QED

(* i2w INT256_MIN <> 0w - 1w *)
Triviality slt_never_ne_max[local]:
  i2w INT256_MIN <> (0w - 1w : bytes32)
Proof
  rewrite_tac[wordsTheory.word_sub_def, wordsTheory.WORD_ADD_0] >>
  strip_tac >>
  `w2i (i2w INT256_MIN : bytes32) = w2i (-1w : bytes32)` by gvs[] >>
  pop_assum mp_tac >>
  rewrite_tac[integer_wordTheory.w2i_minus_1, INT256_MIN_def] >>
  `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  mp_tac (INST_TYPE [alpha |-> ``:256``]
          integer_wordTheory.INT_ZERO_LT_INT_MIN) >>
  rewrite_tac[integer_wordTheory.INT_MIN_def] >> intLib.ARITH_TAC
QED

(* ===== Almost-never: boundary equivalences ===== *)

(* SGT: word_gt x (i2w INT256_MAX - 1w) iff x = i2w INT256_MAX *)
Triviality sgt_almost_never[local]:
  !x:bytes32. word_gt x (i2w INT256_MAX - 1w) <=> (x = i2w INT256_MAX)
Proof
  gen_tac >>
  rewrite_tac[integer_wordTheory.WORD_GTi, INT256_MAX_def] >>
  `i2w (INT_MAX (:256)) - 1w = i2w (INT_MAX (:256) - 1) : bytes32` by (
    ONCE_REWRITE_TAC[GSYM integer_wordTheory.word_sub_i2w] >>
    `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by w2i_i2w_tac >>
    simp[integer_wordTheory.w2i_1]) >>
  pop_assum SUBST_ALL_TAC >>
  `w2i (i2w (INT_MAX (:256) - 1) : bytes32) = INT_MAX (:256) - 1` by
    w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by w2i_i2w_tac >>
  EQ_TAC >| [
    strip_tac >>
    mp_tac (Q.SPEC `x` (INST_TYPE [alpha |-> ``:256``]
            integer_wordTheory.w2i_le)) >>
    strip_tac >>
    `w2i x = INT_MAX (:256)` by intLib.ARITH_TAC >>
    metis_tac[integer_wordTheory.w2i_11],
    strip_tac >>
    qpat_x_assum `x = _` SUBST_ALL_TAC >>
    qpat_x_assum `w2i _ = _` (fn th => rewrite_tac[th]) >>
    intLib.ARITH_TAC
  ]
QED

(* SLT: word_lt x (i2w INT256_MIN + 1w) iff x = i2w INT256_MIN *)
Triviality slt_almost_never[local]:
  !x:bytes32. word_lt x (i2w INT256_MIN + 1w) <=> (x = i2w INT256_MIN)
Proof
  gen_tac >>
  rewrite_tac[integer_wordTheory.WORD_LTi, INT256_MIN_def] >>
  `i2w (INT_MIN (:256)) + 1w = i2w (INT_MIN (:256) + 1) : bytes32` by (
    ONCE_REWRITE_TAC[GSYM integer_wordTheory.word_add_i2w] >>
    `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by w2i_i2w_tac >>
    simp[integer_wordTheory.w2i_1]) >>
  pop_assum SUBST_ALL_TAC >>
  `w2i (i2w (INT_MIN (:256) + 1) : bytes32) = INT_MIN (:256) + 1` by
    w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by w2i_i2w_tac >>
  EQ_TAC >| [
    strip_tac >>
    mp_tac (Q.SPEC `x` (INST_TYPE [alpha |-> ``:256``]
            integer_wordTheory.w2i_ge)) >>
    strip_tac >>
    `w2i x = INT_MIN (:256)` by intLib.ARITH_TAC >>
    metis_tac[integer_wordTheory.w2i_11],
    strip_tac >>
    qpat_x_assum `x = _` SUBST_ALL_TAC >>
    qpat_x_assum `w2i _ = _` (fn th => rewrite_tac[th]) >>
    intLib.ARITH_TAC
  ]
QED

(* ===== Almost-always: boundary equivalences ===== *)

(* SGT: word_gt x (i2w INT256_MIN) iff x <> i2w INT256_MIN *)
Triviality sgt_almost_always[local]:
  !x:bytes32. word_gt x (i2w INT256_MIN) <=> (x <> i2w INT256_MIN)
Proof
  gen_tac >>
  rewrite_tac[integer_wordTheory.WORD_GTi, INT256_MIN_def] >>
  `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  EQ_TAC >| [
    strip_tac >> strip_tac >>
    `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by w2i_i2w_tac >>
    `w2i x = INT_MIN (:256)` by metis_tac[integer_wordTheory.w2i_11] >>
    intLib.ARITH_TAC,
    strip_tac >>
    mp_tac (Q.SPEC `x` (INST_TYPE [alpha |-> ``:256``]
            integer_wordTheory.w2i_ge)) >>
    strip_tac >>
    `w2i (i2w (INT_MIN (:256)) : bytes32) = INT_MIN (:256)` by w2i_i2w_tac >>
    `w2i x <> INT_MIN (:256)` by metis_tac[integer_wordTheory.w2i_11] >>
    intLib.ARITH_TAC
  ]
QED

(* SLT: word_lt x (i2w INT256_MAX) iff x <> i2w INT256_MAX *)
Triviality slt_almost_always[local]:
  !x:bytes32. word_lt x (i2w INT256_MAX) <=> (x <> i2w INT256_MAX)
Proof
  gen_tac >>
  rewrite_tac[integer_wordTheory.WORD_LTi, INT256_MAX_def] >>
  `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by w2i_i2w_tac >>
  pop_assum (fn th => rewrite_tac[th]) >>
  EQ_TAC >| [
    strip_tac >> strip_tac >>
    `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by w2i_i2w_tac >>
    `w2i x = INT_MAX (:256)` by metis_tac[integer_wordTheory.w2i_11] >>
    intLib.ARITH_TAC,
    strip_tac >>
    mp_tac (Q.SPEC `x` (INST_TYPE [alpha |-> ``:256``]
            integer_wordTheory.w2i_le)) >>
    strip_tac >>
    `w2i (i2w (INT_MAX (:256)) : bytes32) = INT_MAX (:256)` by w2i_i2w_tac >>
    `w2i x <> INT_MAX (:256)` by metis_tac[integer_wordTheory.w2i_11] >>
    intLib.ARITH_TAC
  ]
QED

(* ===== Per-opcode comparator sim: shared tactic fragments ===== *)

(* Identity case tactic: replacement = [inst], closes goal or fails *)
val identity_tac =
  DISJ2_TAC >>
  simp[run_insts_def, step_inst_non_invoke] >>
  CASE_TAC >> simp[run_insts_def, lift_result_def,
                   state_equiv_refl, execution_equiv_refl];

(* TRY identity: closes identity goals, leaves non-identity unchanged *)
val try_identity = TRY (identity_tac >> NO_TAC);

(* Self case tactic: op1 = op2 → ASSIGN 0w *)
fun self_tac cmp_thm =
  DISJ2_TAC >>
  simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
       exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op1 s` >> gvs[] >>
  simp[lift_result_def, bool_to_word_def, state_equiv_refl] >>
  gvs[cmp_thm];

(* Never case: cmp x never = 0 → ASSIGN 0w *)
fun never_tac never_thm =
  DISJ2_TAC >>
  `op2 = Lit never_val` by (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
  simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
       exec_pure2_def, eval_operand_def] >>
  Cases_on `eval_operand op1 s` >> gvs[] >>
  simp[lift_result_def, bool_to_word_def, state_equiv_refl, never_thm];

(* ISZERO+ISZERO sim: 1-to-2 expansion via fresh "iz" variable *)
val iszero_iszero_tac =
  simp[LET_THM] >>
  Cases_on `eval_operand op1 s` >> gvs[]
  >- (DISJ1_TAC >> simp[step_inst_base_def, exec_pure2_def, eval_operand_def])
  >>
  DISJ2_TAC >>
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
  qabbrev_tac `tmp = ao_fresh_var inst.inst_id "iz"` >>
  simp[run_insts_def, step_inst_non_invoke] >>
  simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def] >>
  simp[run_insts_def, step_inst_non_invoke] >>
  simp[Once step_inst_base_def, exec_pure1_def,
       eval_operand_update_same] >>
  simp[run_insts_def, bool_to_word_eq_0, lift_result_def] >>
  irule state_equiv_1to2 >> simp[];

(* ===== GT simulation ===== *)

Triviality ao_cmp_sim_gt[local]:
  !fv dfg ra lbl idx inst s fuel ctx.
    inst.inst_opcode = GT /\
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv /\
    ao_opt_cmp_range ra lbl idx inst T F = NONE ==>
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
  simp[ao_opt_comparator_def, ao_unsigned_boundaries_def, LET_THM] >>
  (* Self: op1 = op2 → ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >> Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, cmp_self_false]
  ) >>
  (* ~is_lit_op op2 → identity *)
  IF_CASES_TAC >- (gvs[] >> identity_tac) >>
  (* lit_eq op2 (0w-1w) → never: ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (0w - 1w)` by (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, gt_never]
  ) >>
  (* lit_eq op2 (0w-1w-1w) → almost_never: NOT + ISZERO *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (0w - 1w - 1w)` by (Cases_on `op2` >> gvs[lit_eq_def]) >>
    gvs[] >>
    (* Resolve inner if: 0w-1w = 0w → F *)
    `0w - 1w <> (0w : bytes32)` by
      simp[wordsTheory.word_sub_def, wordsTheory.WORD_ADD_0,
           wordsTheory.word_T_not_zero] >>
    simp[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    qabbrev_tac `tmp = ao_fresh_var inst.inst_id "not"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, word_1comp_eq_0, gt_almost_never,
         lift_result_def] >>
    irule state_equiv_1to2 >> simp[]
  ) >>
  (* prefer_iszero + almost_always=0w → ISZERO(ISZERO(x)) *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit 0w` by (
      fs[] >> Cases_on `op2` >> gvs[lit_eq_def]) >>
    gvs[] >> simp[ao_cmp_prefer_iz_zero_def, LET_THM] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    qabbrev_tac `tmp = ao_fresh_var inst.inst_id "iz"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, bool_to_word_eq_0, gt_zero, lift_result_def] >>
    irule state_equiv_1to2 >> simp[]
  ) >>
  (* GT + lit_eq op2 0w → ISZERO(ISZERO(x)) *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit 0w` by (
      fs[] >> Cases_on `op2` >> gvs[lit_eq_def]) >>
    gvs[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    qabbrev_tac `tmp = ao_fresh_var inst.inst_id "iz"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, bool_to_word_eq_0, gt_zero, lift_result_def] >>
    irule state_equiv_1to2 >> simp[]
  ) >>
  (* Fallback → identity *)
  gvs[] >> identity_tac
QED

(* ===== LT simulation ===== *)

Triviality ao_cmp_sim_lt[local]:
  !fv dfg ra lbl idx inst s fuel ctx.
    inst.inst_opcode = LT /\
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv /\
    ao_opt_cmp_range ra lbl idx inst F F = NONE ==>
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
  simp[ao_opt_comparator_def, ao_unsigned_boundaries_def, LET_THM] >>
  (* Self: op1 = op2 → ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >> Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, cmp_self_false]
  ) >>
  (* ~is_lit_op op2 → identity *)
  IF_CASES_TAC >- (gvs[] >> identity_tac) >>
  (* lit_eq op2 0w → never: ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit 0w` by (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, lt_never]
  ) >>
  (* lit_eq op2 1w → almost_never: never=0w → ISZERO *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit 1w` by (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, exec_pure1_def,
         eval_operand_def, run_insts_def, step_inst_non_invoke,
         lt_almost_never, lift_result_def, bool_to_word_def,
         state_equiv_refl]
  ) >>
  (* prefer_iszero + almost_always=0w-1w → NOT+ISZERO+ISZERO *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (0w - 1w)` by (
      fs[] >> Cases_on `op2` >> gvs[lit_eq_def]) >>
    gvs[] >>
    (* Resolve inner ifs: val_w = 0w → F, val_w = 0w-1w → T *)
    `0w - 1w <> (0w : bytes32)` by
      simp[wordsTheory.word_sub_def, wordsTheory.WORD_ADD_0,
           wordsTheory.word_T_not_zero] >>
    simp[ao_cmp_prefer_iz_max_def, LET_THM] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    qabbrev_tac `tmp_not = ao_fresh_var inst.inst_id "not"` >>
    qabbrev_tac `tmp_iz = ao_fresh_var inst.inst_id "iz"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_def, lookup_var_update] >>
    simp[run_insts_def, word_1comp_eq_0, bool_to_word_eq_0,
         lt_max, lift_result_def] >>
    irule state_equiv_1to3 >> simp[]
  ) >>
  (* GT-specific: not applicable for LT *)
  (* Fallback → identity *)
  gvs[] >> TRY (IF_CASES_TAC >> gvs[]) >> identity_tac
QED

(* ===== SGT simulation ===== *)
Triviality ao_cmp_sim_sgt[local]:
  !fv dfg ra lbl idx inst s fuel ctx.
    inst.inst_opcode = SGT /\
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv /\
    ao_opt_cmp_range ra lbl idx inst T T = NONE ==>
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
  simp[ao_opt_comparator_def, ao_signed_boundaries_def, LET_THM] >>
  (* Self: op1 = op2 -> ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >> Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, cmp_self_false]
  ) >>
  (* ~is_lit_op op2 -> identity *)
  IF_CASES_TAC >- (gvs[] >> identity_tac) >>
  (* lit_eq op2 (i2w INT256_MAX) -> never: ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (i2w INT256_MAX)` by
      (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, sgt_never]
  ) >>
  (* lit_eq op2 (i2w INT256_MAX - 1w) -> almost_never: EQ(op1, never) *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (i2w INT256_MAX - 1w)` by
      (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    (* Resolve inner ifs: never = i2w INT256_MAX <> 0w and <> 0w-1w *)
    simp[sgt_never_ne_0, sgt_never_ne_max] >>
    (* Replacement: EQ(op1, Lit (i2w INT256_MAX)) - single instruction *)
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, sgt_almost_never, lift_result_def,
         state_equiv_refl]
  ) >>
  (* prefer_iszero + almost_always = i2w INT256_MIN *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (i2w INT256_MIN)` by (
      fs[] >> Cases_on `op2` >> gvs[lit_eq_def]) >>
    gvs[] >>
    (* Resolve inner ifs: val_w = i2w INT256_MIN <> 0w and <> 0w-1w *)
    simp[slt_never_ne_0, slt_never_ne_max,
         ao_cmp_prefer_iz_general_def, LET_THM] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    qabbrev_tac `tmp_xor = ao_fresh_var inst.inst_id "xor"` >>
    qabbrev_tac `tmp_iz = ao_fresh_var inst.inst_id "iz"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_def, lookup_var_update] >>
    simp[run_insts_def, word_xor_eq_0, bool_to_word_eq_0,
         sgt_almost_always, lift_result_def] >>
    irule state_equiv_1to3 >> simp[]
  ) >>
  (* GT-specific case: SGT <> GT, so F *)
  (* Fallback -> identity *)
  gvs[] >> TRY (IF_CASES_TAC >> gvs[]) >> identity_tac
QED

(* ===== SLT simulation ===== *)
Triviality ao_cmp_sim_slt[local]:
  !fv dfg ra lbl idx inst s fuel ctx.
    inst.inst_opcode = SLT /\
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv /\
    ao_opt_cmp_range ra lbl idx inst F T = NONE ==>
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
  simp[ao_opt_comparator_def, ao_signed_boundaries_def, LET_THM] >>
  (* Self: op1 = op2 -> ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >> Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, cmp_self_false]
  ) >>
  (* ~is_lit_op op2 -> identity *)
  IF_CASES_TAC >- (gvs[] >> identity_tac) >>
  (* lit_eq op2 (i2w INT256_MIN) -> never: ASSIGN 0w *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (i2w INT256_MIN)` by
      (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
         exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, lift_result_def, bool_to_word_def,
         state_equiv_refl, slt_never]
  ) >>
  (* lit_eq op2 (i2w INT256_MIN + 1w) -> almost_never: EQ(op1, never) *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (i2w INT256_MIN + 1w)` by
      (Cases_on `op2` >> gvs[lit_eq_def]) >> gvs[] >>
    (* Resolve inner ifs: never = i2w INT256_MIN <> 0w and <> 0w-1w *)
    simp[slt_never_ne_0, slt_never_ne_max] >>
    (* Replacement: EQ(op1, Lit (i2w INT256_MIN)) - single instruction *)
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, slt_almost_never, lift_result_def,
         state_equiv_refl]
  ) >>
  (* prefer_iszero + almost_always = i2w INT256_MAX *)
  IF_CASES_TAC >- (
    gvs[] >>
    `op2 = Lit (i2w INT256_MAX)` by (
      fs[] >> Cases_on `op2` >> gvs[lit_eq_def]) >>
    gvs[] >>
    (* Resolve inner ifs: val_w = i2w INT256_MAX <> 0w and <> 0w-1w *)
    simp[sgt_never_ne_0, sgt_never_ne_max,
         ao_cmp_prefer_iz_general_def, LET_THM] >>
    Cases_on `eval_operand op1 s` >> gvs[]
    >- (DISJ1_TAC >>
        simp[step_inst_base_def, exec_pure2_def, eval_operand_def]) >>
    DISJ2_TAC >>
    simp[step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    qabbrev_tac `tmp_xor = ao_fresh_var inst.inst_id "xor"` >>
    qabbrev_tac `tmp_iz = ao_fresh_var inst.inst_id "iz"` >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure2_def, eval_operand_def] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_update_same] >>
    simp[run_insts_def, step_inst_non_invoke] >>
    simp[Once step_inst_base_def, exec_pure1_def,
         eval_operand_def, lookup_var_update] >>
    simp[run_insts_def, word_xor_eq_0, bool_to_word_eq_0,
         slt_almost_always, lift_result_def] >>
    irule state_equiv_1to3 >> simp[]
  ) >>
  (* GT-specific case: SLT <> GT, so F *)
  (* Fallback -> identity *)
  gvs[] >> TRY (IF_CASES_TAC >> gvs[]) >> identity_tac
QED

(* ===== Main comparator simulation theorem ===== *)

Theorem ao_cmp_sim:
  !fv dfg ra lbl idx inst s fuel ctx.
    (inst.inst_opcode = GT \/ inst.inst_opcode = LT \/
     inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) /\
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    ao_fresh_var inst.inst_id "not" IN fv /\
    ao_fresh_var inst.inst_id "iz" IN fv /\
    ao_fresh_var inst.inst_id "xor" IN fv /\
    ao_opt_cmp_range ra lbl idx inst
      (inst.inst_opcode = GT \/ inst.inst_opcode = SGT)
      (inst.inst_opcode = SGT \/ inst.inst_opcode = SLT) = NONE ==>
    (?e. step_inst_base inst s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (step_inst_base inst s)
      (run_insts fuel ctx (ao_opt_comparator dfg ra lbl idx inst) s)
Proof
  rpt strip_tac >> gvs[]
  >- (irule ao_cmp_sim_gt >> simp[])
  >- (irule ao_cmp_sim_lt >> simp[])
  >- (irule ao_cmp_sim_sgt >> simp[])
  >- (irule ao_cmp_sim_slt >> simp[])
QED

val _ = export_theory();
