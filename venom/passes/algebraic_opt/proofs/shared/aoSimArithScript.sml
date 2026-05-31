(*
 * Algebraic Optimization — Arithmetic Opcode Simulation Helpers
 *
 * TOP-LEVEL:
 *   ao_signextend_sim — SIGNEXTEND branches produce equiv or error
 *   ao_exp_sim        — Exp branches produce equiv or error
 *   ao_sdiv_sim       — SDIV (via muldiv) produces equiv or error
 *   ao_smod_sim       — SMOD (via muldiv) produces equiv or error
 *)
Theory aoSimArith
Ancestors
  algebraicOptDefs aoRules aoRules2
  venomExecSemantics venomState venomInst passSharedDefs
  valueRangeDefs rangeAnalysisDefs
Libs
  pairLib BasicProvers intLib wordsLib

(* ===== Word division zero helpers ===== *)

(* 0w / c = 0w (signed word division, for c ≠ 0w) *)
Triviality word_quot_zero_l[local]:
  !c : 'a word. c <> 0w ==> 0w / c = 0w
Proof
  rpt strip_tac >>
  simp[integer_wordTheory.word_quot, integer_wordTheory.word_0_w2i,
       integerTheory.INT_QUOT_0] >>
  `w2i c <> 0` by (
    strip_tac >> gvs[integer_wordTheory.w2i_eq_0]) >>
  simp[integerTheory.INT_QUOT_0, integer_wordTheory.i2w_def]
QED

(* 0w rem c = 0w (signed word remainder, for c ≠ 0w) *)
Triviality word_rem_zero_l[local]:
  !c : 'a word. c <> 0w ==> word_rem 0w c = 0w
Proof
  rpt strip_tac >>
  simp[integer_wordTheory.word_rem, integer_wordTheory.word_0_w2i] >>
  `w2i c <> 0` by (
    strip_tac >> gvs[integer_wordTheory.w2i_eq_0]) >>
  simp[integerTheory.INT_REM0, integer_wordTheory.i2w_def]
QED

(* x / 1w = x (signed word division by 1) *)
Triviality w2i_1w_256[local]:
  w2i (1w : bytes32) = 1
Proof
  `~word_msb (1w : bytes32)` by wordsLib.WORD_DECIDE_TAC >>
  simp[integer_wordTheory.w2i_eq_w2n]
QED

Triviality word_quot_one[local]:
  !x : bytes32. x / 1w = x
Proof
  gen_tac >>
  `1w <> (0w : bytes32)` by simp[] >>
  simp[integer_wordTheory.word_quot, w2i_1w_256,
       integerTheory.INT_QUOT_1, integer_wordTheory.i2w_w2i]
QED

(* word_rem x 1w = 0w *)
Triviality int_rem_1[local]:
  !p:int. p rem 1 = 0
Proof
  gen_tac >>
  mp_tac (Q.SPEC `1` integerTheory.INT_REMQUOT) >>
  impl_tac >- simp[] >>
  disch_then (qspec_then `p` strip_assume_tac) >>
  intLib.ARITH_TAC
QED

Triviality word_rem_one[local]:
  !x : bytes32. word_rem x 1w = 0w
Proof
  gen_tac >>
  `1w <> (0w : bytes32)` by simp[] >>
  simp[integer_wordTheory.word_rem, w2i_1w_256, int_rem_1,
       integer_wordTheory.i2w_def]
QED

(* ===== step_inst_base dispatch helpers ===== *)


(* ===== Operand decomposition helper ===== *)

Triviality decomp_2_1[local]:
  !ops outs.
    LENGTH ops = 2 /\ LENGTH outs = 1 ==>
    ?op1 op2 out. ops = [op1; op2] /\ outs = [out]
Proof
  rpt gen_tac >> strip_tac >>
  `?a1 rest. ops = a1 :: rest` by (Cases_on `ops` >> gvs[]) >>
  `?a2 rest2. rest = a2 :: rest2` by (Cases_on `rest` >> gvs[]) >>
  `rest2 = []` by gvs[] >>
  `?o1 rest3. outs = o1 :: rest3` by (Cases_on `outs` >> gvs[]) >>
  `rest3 = []` by gvs[] >>
  gvs[]
QED

(* ===== SIGNEXTEND ===== *)

(* Word-level: w && n2w(2^k - 1) = w when w2n w < 2^k *)
Triviality and_mask_id[local]:
  !w:'a word k.
    w2n w < 2 ** k ==>
    w && n2w (2 ** k - 1) = w
Proof
  rpt strip_tac >>
  `w = n2w (w2n w)` by simp[wordsTheory.n2w_w2n] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[wordsTheory.WORD_AND_EXP_SUB1]
QED

(* Helper: complement bound from negative word range *)
Triviality neg_comp_lt_exp[local]:
  !(w : bytes32) bp.
    word_msb w /\ -&(2 ** bp) <= w2i w ==>
    w2n (word_1comp w) < 2 ** bp
Proof
  rpt gen_tac >> strip_tac >>
  `w <> 0w` by (
    strip_tac >>
    qpat_x_assum `word_msb _` mp_tac >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[wordsTheory.WORD_0_POS]) >>
  `w2i w = -&(w2n(-w))` by (
    qpat_x_assum `w <> 0w` kall_tac >>
    qpat_x_assum `word_msb w`
      (fn msb => REWRITE_TAC[integer_wordTheory.w2i_def, msb])) >>
  `w2n (-w) <= 2 ** bp` by (
    qpat_x_assum `-_ <= w2i w` mp_tac >>
    qpat_x_assum `w2i w = _` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >> intLib.ARITH_TAC) >>
  `word_1comp w <> UINT_MAXw` by (
    strip_tac >>
    qpat_x_assum `w <> 0w` mp_tac >> pop_assum mp_tac >>
    rpt (pop_assum kall_tac) >>
    PURE_REWRITE_TAC[GSYM wordsTheory.WORD_NOT_0] >>
    rpt strip_tac >> metis_tac[wordsTheory.WORD_NOT_NOT]) >>
  `w2n (word_1comp w) + 1 = w2n (-w)` by (
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [wordsTheory.WORD_NEG])) >>
    qpat_x_assum `word_1comp w <> _` mp_tac >>
    rpt (pop_assum kall_tac) >> strip_tac >>
    mp_tac (SPEC ``word_1comp (w:bytes32)``
            (INST_TYPE [alpha |-> ``:256``] wordsTheory.w2n_plus1)) >>
    ASM_REWRITE_TAC[]) >>
  qpat_x_assum `w2n (-w) <= _` mp_tac >>
  pop_assum mp_tac >> rpt (pop_assum kall_tac) >>
  rpt strip_tac >> DECIDE_TAC
QED

(* Helper: OR with complement of mask identity *)
Triviality or_comp_mask_id[local]:
  !(w : 'a word) k.
    w2n (word_1comp w) < 2 ** k ==>
    w || word_1comp (n2w (2 ** k - 1)) = w
Proof
  rpt strip_tac >>
  `word_1comp w && n2w (2 ** k - 1) = word_1comp w` by (
    irule and_mask_id >> first_assum ACCEPT_TAC) >>
  `word_1comp (word_1comp w && n2w (2 ** k - 1)) =
   word_1comp (word_1comp w)` by (AP_TERM_TAC >> first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >>
  PURE_REWRITE_TAC[wordsTheory.WORD_DE_MORGAN_THM, wordsTheory.WORD_NOT_NOT] >>
  DISCH_THEN ACCEPT_TAC
QED

(* Helper: sign bit from complement lsr = 0 *)
Triviality lsr_comp_zero_and_1[local]:
  !(w : 'a word) k.
    word_1comp w >>> k = 0w /\ k < dimindex(:'a) ==>
    w >>> k && 1w = 1w
Proof
  rpt gen_tac >> strip_tac >>
  (* w >>> k = UINT_MAXw >>> k via OR complement *)
  `w >>> k = UINT_MAXw >>> k` by (
    `w >>> k || word_1comp w >>> k = UINT_MAXw >>> k` by
      REWRITE_TAC[wordsTheory.LSR_BITWISE, wordsTheory.WORD_OR_COMP] >>
    pop_assum mp_tac >>
    ASM_REWRITE_TAC[wordsTheory.WORD_OR_CLAUSES]) >>
  pop_assum SUBST1_TAC >>
  (* UINT_MAXw >>> k && 1w = 1w via FCP *)
  PURE_REWRITE_TAC[GSYM wordsTheory.WORD_NEG_1] >>
  simp[fcpTheory.CART_EQ, wordsTheory.word_and_def,
       wordsTheory.word_lsr_def, fcpTheory.FCP_BETA,
       wordsTheory.word_index, wordsTheory.WORD_NEG_1_T] >>
  gen_tac >> strip_tac >>
  Cases_on `i`
  >- simp[wordsTheory.WORD_NEG_1_T]
  >- simp[]
QED

(* sign_extend n w = w when w2i w fits in 8*(w2n n + 1) signed bits *)
Triviality sign_extend_in_range[local]:
  !n w : bytes32.
    w2n n <= 30 /\
    ~(&(2 ** (w2n n * 8 + 7))) <= w2i w /\
    w2i w <= &(2 ** (w2n n * 8 + 7)) - 1 ==>
    sign_extend n w = w
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `bp = w2n n * 8 + 7` >>
  PURE_ONCE_REWRITE_TAC[sign_extend_def] >>
  `~(w2n n > 30)` by (
    ntac 2 (pop_assum kall_tac) >> pop_assum kall_tac >> simp[]) >>
  PURE_ASM_REWRITE_TAC[] >>
  PURE_REWRITE_TAC[LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  PURE_REWRITE_TAC[COND_CLAUSES] >>
  Cases_on `0 <= w2i w`
  >- (
    (* Positive case *)
    `~word_msb w` by (
      REWRITE_TAC[wordsTheory.word_msb_neg, integer_wordTheory.WORD_LTi,
                  integer_wordTheory.word_0_w2i] >>
      intLib.ARITH_TAC) >>
    `w2i w = &(w2n w)` by (
      pop_assum (fn nmsb =>
        REWRITE_TAC[integer_wordTheory.w2i_def, nmsb])) >>
    `w2n w < 2 ** bp` by intLib.ARITH_TAC >>
    `w >>> bp = 0w` by (
      rewrite_tac[GSYM wordsTheory.w2n_eq_0, wordsTheory.w2n_lsr] >>
      irule arithmeticTheory.LESS_DIV_EQ_ZERO >>
      first_assum ACCEPT_TAC) >>
    markerLib.UNABBREV_TAC "bp" >>
    PURE_ASM_REWRITE_TAC[wordsTheory.WORD_AND_CLAUSES] >>
    PURE_REWRITE_TAC[EVAL ``(0w:bytes32) = 1w``, COND_CLAUSES] >>
    PURE_REWRITE_TAC[wordsTheory.word_1_lsl, wordsTheory.word_sub_def,
                     wordsTheory.WORD_LITERAL_ADD,
                     bitTheory.ONE_LE_TWOEXP, COND_CLAUSES] >>
    irule and_mask_id >>
    irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
    qexists_tac `2 ** (w2n n * 8 + 7)` >>
    PURE_ASM_REWRITE_TAC[] >>
    PURE_REWRITE_TAC[AND_CLAUSES] >>
    irule bitTheory.TWOEXP_MONO2 >>
    rpt (pop_assum kall_tac) >> DECIDE_TAC)
  >- (
    (* Negative case *)
    `word_msb w` by (
      REWRITE_TAC[wordsTheory.word_msb_neg, integer_wordTheory.WORD_LTi,
                  integer_wordTheory.word_0_w2i] >>
      intLib.ARITH_TAC) >>
    `w2n (word_1comp w) < 2 ** bp` by (
      irule neg_comp_lt_exp >> conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC) >>
    `word_1comp w >>> bp = 0w` by (
      rewrite_tac[GSYM wordsTheory.w2n_eq_0, wordsTheory.w2n_lsr] >>
      irule arithmeticTheory.LESS_DIV_EQ_ZERO >>
      first_assum ACCEPT_TAC) >>
    markerLib.UNABBREV_TAC "bp" >>
    `w >>> (w2n n * 8 + 7) && 1w = 1w` by (
      irule lsr_comp_zero_and_1 >>
      qpat_x_assum `word_1comp w >>> _ = 0w`
        (fn th => REWRITE_TAC[th]) >>
      qpat_x_assum `w2n n <= 30` mp_tac >>
      rpt (pop_assum kall_tac) >> strip_tac >>
      PURE_REWRITE_TAC[EVAL ``dimindex(:256)``] >>
      DECIDE_TAC) >>
    ASM_REWRITE_TAC[] >>
    PURE_REWRITE_TAC[wordsTheory.word_1_lsl, wordsTheory.word_sub_def,
                     wordsTheory.WORD_LITERAL_ADD,
                     bitTheory.ONE_LE_TWOEXP, COND_CLAUSES] >>
    irule or_comp_mask_id >>
    qpat_x_assum `w2n (word_1comp w) < _` mp_tac >>
    rpt (pop_assum kall_tac) >> strip_tac >>
    irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
    qexists_tac `2 ** (w2n n * 8 + 7)` >>
    PURE_ASM_REWRITE_TAC[] >>
    PURE_REWRITE_TAC[AND_CLAUSES] >>
    irule bitTheory.TWOEXP_MONO2 >>
    rpt (pop_assum kall_tac) >> DECIDE_TAC)
QED

(* Helper: derive w2i bounds from in_range + vr_lo/vr_hi bounds *)
Triviality in_range_bounds[local]:
  !r (v:bytes32) (bound:num).
    in_range r v /\ ~vr_is_top r /\
    vr_lo r >= -&bound /\ vr_hi r <= &bound - 1 ==>
    -&bound <= w2i v /\ w2i v <= &bound - 1
Proof
  Cases_on `r` >>
  REWRITE_TAC[in_range_def, vr_is_top_def, vr_lo_def, vr_hi_def] >>
  TRY (REWRITE_TAC[] >> NO_TAC) >>
  REWRITE_TAC[integerTheory.int_ge] >>
  rpt strip_tac >> metis_tac[integerTheory.INT_LE_TRANS]
QED


Theorem ao_signextend_sim:
  !ra lbl idx inst0 s.
    inst0.inst_opcode = SIGNEXTEND /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 /\
    (!op v. MEM op inst0.inst_operands /\
            eval_operand op s = SOME v ==>
            in_range (range_get_range ra lbl idx op) v) ==>
    step_inst_base (HD (ao_opt_signextend ra lbl idx inst0)) s =
      step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  simp[ao_opt_signextend_def, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  TRY (DISJ1_TAC >> metis_tac[ao_rule_signextend_ge31]) >>
  (* Range-based goals: prove sign_extend fact, then unfold *)
  DISJ1_TAC >>
  qmatch_goalsub_abbrev_tac
    `inst0 with <|inst_opcode := ASSIGN; inst_operands := [xop]|>` >>
  `!v. eval_operand xop s = SOME v ==> sign_extend c v = v` by (
    rpt strip_tac >>
    `in_range (range_get_range ra lbl idx xop) v` by (
      first_x_assum irule >> ASM_REWRITE_TAC[]) >>
    drule_all in_range_bounds >> strip_tac >>
    irule sign_extend_in_range >>
    `8 * (w2n c + 1) - 1 = w2n c * 8 + 7` by (
      qpat_x_assum `w2n c < 31` mp_tac >>
      rpt (pop_assum kall_tac) >> strip_tac >> DECIDE_TAC) >>
    rpt conj_tac
    >- (qpat_x_assum `w2n c < 31` mp_tac >>
        rpt (pop_assum kall_tac) >> strip_tac >> DECIDE_TAC)
    >- (pop_assum (fn eq => PURE_REWRITE_TAC[GSYM eq]) >>
        first_assum ACCEPT_TAC)
    >- (qpat_x_assum `_ = w2n c * 8 + 7`
          (fn eq => PURE_REWRITE_TAC[GSYM eq]) >>
        first_assum ACCEPT_TAC)) >>
  (* Clear exponentials, now safe to use simp *)
  markerLib.UNABBREV_TAC "xop" >>
  rpt (qpat_x_assum `vr_hi _ <= _` kall_tac) >>
  rpt (qpat_x_assum `vr_lo _ >= _` kall_tac) >>
  rpt (qpat_x_assum `~vr_is_top _` kall_tac) >>
  rpt (qpat_x_assum `_ < 31` kall_tac) >>
  rpt (qpat_x_assum `~(_ >= _)` kall_tac) >>
  rpt (qpat_x_assum `!op v. _` kall_tac) >>
  simp[step_inst_base_def, exec_pure2_def, exec_pure1_def,
       eval_operand_def] >>
  every_case_tac >> gvs[eval_operand_def]
QED

(* ===== Exp ===== *)

Theorem ao_exp_sim:
  !inst0 s.
    inst0.inst_opcode = Exp /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_exp inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_exp_def, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Brute force: unfold step_inst_base for both sides *)
  simp[step_inst_base_def, exec_pure2_def, exec_pure1_def,
       eval_operand_def] >>
  every_case_tac >> gvs[wordsTheory.word_exp_def,
    arithmeticTheory.EXP_1, arithmeticTheory.ZERO_EXP] >>
  rpt IF_CASES_TAC >> gvs[bool_to_word_def]
QED

(* ===== SDIV ===== *)

(* For the zero case: safe_sdiv with a literal 0 operand gives 0.
   - safe_sdiv v 0w = 0w (by definition)
   - safe_sdiv 0w v = 0w / v = 0w (when v ≠ 0w, 0 quot v = 0) *)
Theorem ao_sdiv_sim:
  !inst0 s.
    inst0.inst_opcode = SDIV /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_muldiv inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Brute force: unfold step_inst_base for both sides *)
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def,
       safe_sdiv_def] >>
  every_case_tac >>
  gvs[safe_sdiv_def, word_quot_zero_l, word_quot_one]
QED

(* ===== SMOD ===== *)

Theorem ao_smod_sim:
  !inst0 s.
    inst0.inst_opcode = SMOD /\
    LENGTH inst0.inst_operands = 2 /\
    LENGTH inst0.inst_outputs = 1 ==>
    step_inst_base (HD (ao_opt_muldiv inst0)) s = step_inst_base inst0 s \/
    ?e. step_inst_base inst0 s = Error e
Proof
  rpt strip_tac >>
  imp_res_tac decomp_2_1 >> gvs[] >>
  Cases_on `op1` >> Cases_on `op2` >>
  gvs[ao_opt_muldiv_def, LET_THM, lit_eq_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  TRY (simp[] >> NO_TAC) >>
  (* Brute force: unfold step_inst_base for both sides *)
  simp[step_inst_base_def, exec_pure2_def, eval_operand_def,
       safe_smod_def] >>
  every_case_tac >>
  gvs[safe_smod_def, word_rem_zero_l, word_rem_one]
QED

val _ = export_theory();
