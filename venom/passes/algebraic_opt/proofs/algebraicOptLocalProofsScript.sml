Theory algebraicOptLocalProofs
Ancestors
  algebraicOptDefs venomExecSemantics venomState stateFrame algebraicOptRangeLocalProofs

(* Successful source evaluation supplies the definedness needed when an
   identity drops an operand. *)
Theorem ao_opt_shift_correct:
  !inst s t out.
    (inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/
     inst.inst_opcode = SAR) /\
    step_inst_base inst s = OK t /\
    MEM out (ao_opt_shift inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_shift_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_shift_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_shift_def] >>
  Cases_on `a` >>
  gvs[passSharedDefsTheory.lit_eq_def] >>
  Cases_on `c = 0w` >> gvs[] >>
  Cases_on `inst` >> gvs[] >>
  qpat_x_assum `step_inst_base _ s = OK t` mp_tac >>
  asm_simp_tac (srw_ss()) [Once step_inst_base_def] >>
  gvs[exec_pure2_def, exec_pure1_def, eval_operand_def,
      AllCaseEqs()] >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once step_inst_base_def] >>
  gvs[exec_pure1_def, wordsTheory.SHIFT_ZERO]
QED


fun local_opcode_eqs opcs = List.filter
  (fn th => let val opc = rhs (fst (dest_imp (concl (SPEC_ALL th))))
            in List.exists (aconv opc) opcs end)
  (CONJUNCTS step_inst_base_opcode_eqs);

Theorem ao_opt_and_correct:
  !inst s t out.
    inst.inst_opcode = AND /\ step_inst_base inst s = OK t /\
    MEM out (ao_opt_and inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_and_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_and_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_and_def] >>
  Cases_on `lit_eq b (0w - 1w)` >> gvs[] >>
  Cases_on `lit_eq a 0w \/ lit_eq b 0w` >> gvs[] >>
  gvs (local_opcode_eqs [``venomInst$AND``, ``venomInst$ASSIGN``]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  gvs[passSharedDefsTheory.lit_eq_def, AllCaseEqs()] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[eval_operand_def] >>
  gvs[exec_pure1_def,
      wordsTheory.WORD_AND_CLAUSES, wordsTheory.WORD_NEG_1,
      wordsTheory.WORD_SUB_LZERO,
      wordsTheory.WORD_EQ_SUB_ZERO]
QED

Theorem ao_opt_addsub_correct:
  !inst s t out.
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = XOR) /\
    step_inst_base inst s = OK t /\ MEM out (ao_opt_addsub inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  (Cases_on `inst.inst_operands` >> gvs[ao_opt_addsub_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_addsub_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_addsub_def] >>
  Cases_on `(inst.inst_opcode = SUB \/ inst.inst_opcode = XOR) /\ a = b`
  >- (gvs[ao_opt_addsub_def] >>
      gvs (local_opcode_eqs [``venomInst$SUB``, ``venomInst$XOR``, ``venomInst$ASSIGN``]) >>
      gvs[exec_pure2_def, AllCaseEqs(), exec_pure1_def, eval_operand_def,
          wordsTheory.WORD_SUB_REFL, wordsTheory.WORD_XOR_CLAUSES]) >>
  Cases_on `lit_eq b 0w`
  >- (gvs[ao_opt_addsub_def] >>
      gvs (local_opcode_eqs [``venomInst$ADD``, ``venomInst$SUB``, ``venomInst$XOR``, ``venomInst$ASSIGN``]) >>
      gvs[exec_pure2_def, AllCaseEqs()] >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def, exec_pure1_def,
          wordsTheory.WORD_XOR_CLAUSES]) >>
  Cases_on `inst.inst_opcode = SUB /\ lit_eq a (0w - 1w)`
  >- (gvs[ao_opt_addsub_def, wordsTheory.WORD_SUB_LZERO] >>
      gvs (local_opcode_eqs [``venomInst$SUB``, ``venomInst$NOT``]) >>
      gvs[exec_pure2_def, AllCaseEqs()] >>
      Cases_on `a` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def, exec_pure1_def,
          wordsTheory.WORD_SUB_LZERO] >>
      simp[wordsTheory.WORD_NOT]) >>
  Cases_on `inst.inst_opcode = XOR /\ lit_eq b (0w - 1w)`
  >- (gvs[ao_opt_addsub_def, wordsTheory.WORD_SUB_LZERO] >>
      gvs (local_opcode_eqs [``venomInst$XOR``, ``venomInst$NOT``]) >>
      gvs[exec_pure2_def, AllCaseEqs()] >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def, exec_pure1_def,
          wordsTheory.WORD_XOR_CLAUSES]) >>
  gvs[ao_opt_addsub_def])
QED

Theorem ao_opt_exp_correct:
  !inst s t out.
    inst.inst_opcode = Exp /\ step_inst_base inst s = OK t /\
    MEM out (ao_opt_exp inst) ==> step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_exp_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_exp_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_exp_def] >>
  Cases_on `lit_eq b 0w` >> gvs[] >>
  Cases_on `lit_eq b 1w` >> gvs[] >>
  Cases_on `lit_eq a 1w` >> gvs[] >>
  Cases_on `lit_eq a 0w` >> gvs[] >>
  gvs (local_opcode_eqs [``venomInst$Exp``, ``venomInst$ASSIGN``, ``venomInst$ISZERO``]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def, AllCaseEqs()] >>
  gvs[exec_pure1_def, eval_operand_def, wordsTheory.word_exp_def,
      arithmeticTheory.ZERO_EXP, bool_to_word_def,
      wordsTheory.w2n_eq_0] >>
  Cases_on `v2 = 0w` >> gvs[bool_to_word_def]
QED

(* The only permitted inexact result is truthification to one.  Both results
   are writes to the same output over the same original frame. *)
Theorem ao_opt_or_correct:
  !dfg inst s t out.
    inst.inst_opcode = OR /\ step_inst_base inst s = OK t /\
    MEM out (ao_opt_or dfg inst) ==>
    ?x v w. inst.inst_outputs = [x] /\ t = update_var x v s /\
      step_inst_base out s = OK (update_var x w s) /\
      (v = 0w <=> w = 0w) /\
      (w = v \/ (ao_all_truthy dfg inst /\ w = 1w /\ v <> 0w))
Proof
  rpt gen_tac >> strip_tac >>
  gvs (local_opcode_eqs [``venomInst$OR``]) >>
  gvs[exec_pure2_def, AllCaseEqs()] >>
  rename1 `inst.inst_operands = [a; b]` >>
  Cases_on `lit_eq b (0w - 1w)`
  >- (gvs[ao_opt_or_def] >>
      gvs (local_opcode_eqs [``venomInst$ASSIGN``]) >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def] >>
      qexistsl [`-1w`, `-1w`] >>
      simp[exec_pure1_def, eval_operand_def,
           wordsTheory.WORD_SUB_LZERO, wordsTheory.WORD_NEG_1,
           wordsTheory.WORD_OR_CLAUSES]) >>
  Cases_on `ao_all_truthy dfg inst /\ is_lit_op b /\ ~lit_eq b 0w`
  >- (gvs[ao_opt_or_def] >>
      gvs (local_opcode_eqs [``venomInst$ASSIGN``]) >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, passSharedDefsTheory.is_lit_op_def,
          eval_operand_def] >>
      gvs[exec_pure1_def, eval_operand_def] >>
      `word_or v1 c <> 0w` by
        (strip_tac >>
         qspecl_then [`c`, `v1`] mp_tac wordsTheory.WORD_OR_ABSORB >>
         gvs[wordsTheory.WORD_OR_COMM, wordsTheory.WORD_AND_CLAUSES]) >>
      `(1w : 256 word) <> 0w` by simp[] >>
      qexistsl [`word_or v1 c`, `1w`] >> simp[]) >>
  Cases_on `lit_eq b 0w`
  >- (gvs[ao_opt_or_def] >>
      gvs (local_opcode_eqs [``venomInst$ASSIGN``]) >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def] >>
      gvs[exec_pure1_def, wordsTheory.WORD_OR_CLAUSES] >> metis_tac[]) >>
  gvs[ao_opt_or_def] >>
  gvs (local_opcode_eqs [``venomInst$OR``]) >>
  gvs[exec_pure2_def] >> metis_tac[]
QED

(* The top set bit survives subtraction of one unless it was the only bit. *)
Theorem ao_power_of_two_value:
  !w:bytes32. is_power_of_two w ==>
    w2n w = 2 ** LOG2 (w2n w)
Proof
  rpt strip_tac >>
  gvs[passSharedDefsTheory.is_power_of_two_def] >>
  `0 < w2n w` by metis_tac[arithmeticTheory.NOT_ZERO_LT_ZERO, wordsTheory.w2n_eq_0] >>
  `LOG2 (w2n w) < 256` by
    (drule wordsTheory.LOG2_w2n_lt >>
     simp[fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  `2 ** LOG2 (w2n w) <= w2n w /\
   w2n w < 2 ** SUC (LOG2 (w2n w))` by
    (drule logrootTheory.LOG2_PROPERTY >>
     simp[GSYM bitTheory.LOG2_def]) >>
  `w - 1w = n2w (w2n w - 1)` by
    simp[wordsTheory.n2w_sub] >>
  `w ' (LOG2 (w2n w))` by
    (mp_tac (Q.SPECL [`w2n (w:bytes32)`, `LOG2 (w2n (w:bytes32))`]
      (INST_TYPE [alpha |-> ``:256``] wordsTheory.word_index_n2w)) >>
     simp[fcpLib.INDEX_CONV ``dimindex(:256)``, bitTheory.BIT_LOG2]) >>
  `(n2w (w2n w - 1):bytes32) ' (LOG2 (w2n w)) =
     BIT (LOG2 (w2n w)) (w2n w - 1)` by
    (mp_tac (Q.SPECL [`w2n (w:bytes32) - 1`, `LOG2 (w2n (w:bytes32))`]
      (INST_TYPE [alpha |-> ``:256``] wordsTheory.word_index_n2w)) >>
     simp[fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  `~BIT (LOG2 (w2n w)) (w2n w - 1)` by
    (qpat_x_assum `word_and _ _ = _` (mp_tac o
      Q.AP_TERM `word_bit (LOG2 (w2n (w:bytes32)))`) >>
     simp[wordsTheory.word_bit_def, wordsTheory.word_and_def,
          fcpLib.INDEX_CONV ``dimindex(:256)``,
          fcpTheory.FCP_BETA, wordsTheory.word_index,
          wordsTheory.word_index_n2w, bitTheory.BIT_LOG2, bitTheory.BIT_ZERO] >>
     pure_rewrite_tac[GSYM wordsTheory.word_sub_def] >>
     asm_rewrite_tac[]) >>
  spose_not_then assume_tac >>
  `2 ** LOG2 (w2n w) <= w2n w - 1` by decide_tac >>
  `0 < w2n w - 1` by
    (mp_tac (Q.SPEC `LOG2 (w2n (w:bytes32))` bitTheory.ZERO_LT_TWOEXP) >>
     decide_tac) >>
  `LOG2 (w2n w) <= LOG2 (w2n w - 1)` by
    metis_tac[bitTheory.TWOEXP_LE_IMP_LE_LOG2] >>
  `LOG2 (w2n w - 1) < SUC (LOG2 (w2n w))` by
    (`w2n w - 1 < 2 ** SUC (LOG2 (w2n w))` by decide_tac >>
     qpat_x_assum `w2n w - 1 < _` mp_tac >>
     pure_rewrite_tac[bitTheory.LT_TWOEXP] >> simp[]) >>
  `LOG2 (w2n w - 1) = LOG2 (w2n w)` by decide_tac >>
  `w2n w - 1 <> 0` by decide_tac >>
  drule bitTheory.BIT_LOG2 >> gvs[]
QED

Theorem ao_power_of_two_log:
  !w:bytes32. is_power_of_two w ==>
    w2n (passSharedDefs$word_log2 w) < 256 /\
    w = n2w (2 ** w2n (passSharedDefs$word_log2 w))
Proof
  rpt strip_tac >>
  `w <> 0w` by gvs[passSharedDefsTheory.is_power_of_two_def] >>
  drule wordsTheory.LOG2_w2n_lt >>
  simp[fcpLib.INDEX_CONV ``dimindex(:256)``] >> strip_tac >>
  `LOG2 (w2n w) < dimword(:256)` by
    (simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     decide_tac) >>
  drule ao_power_of_two_value >> strip_tac >>
  simp[passSharedDefsTheory.word_log2_def] >>
  metis_tac[wordsTheory.n2w_w2n]
QED

Theorem ao_power_of_two_mul:
  !(x:bytes32) w. is_power_of_two w ==>
    x * w = x << w2n (passSharedDefs$word_log2 w)
Proof
  rpt strip_tac >> drule ao_power_of_two_log >> strip_tac >>
  rewrite_tac[wordsTheory.WORD_MUL_LSL] >>
  metis_tac[wordsTheory.WORD_MULT_COMM]
QED

Theorem ao_power_of_two_div:
  !(x:bytes32) w. is_power_of_two w ==>
    safe_div x w = x >>> w2n (passSharedDefs$word_log2 w)
Proof
  rpt strip_tac >> drule ao_power_of_two_log >> strip_tac >>
  `w <> 0w` by gvs[passSharedDefsTheory.is_power_of_two_def] >>
  simp[safe_div_def] >>
  `w2n (passSharedDefs$word_log2 w) < dimindex(:256)` by
    simp[fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  drule wordsTheory.WORD_DIV_LSR >>
  disch_then (qspec_then `x` mp_tac) >> metis_tac[]
QED

Theorem ao_power_of_two_mod:
  !(x:bytes32) w. is_power_of_two w ==>
    safe_mod x w = word_and x (w - 1w)
Proof
  rpt strip_tac >> drule ao_power_of_two_value >> strip_tac >>
  `w <> 0w` by gvs[passSharedDefsTheory.is_power_of_two_def] >>
  `0 < w2n w` by metis_tac[wordsTheory.w2n_eq_0,
      arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `w - 1w = n2w (w2n w - 1)` by simp[wordsTheory.n2w_sub] >>
  simp[safe_mod_def, wordsTheory.word_mod_def] >>
  qpat_x_assum `w2n w = _` (fn th => once_rewrite_tac[th]) >>
  metis_tac[wordsTheory.WORD_AND_EXP_SUB1, wordsTheory.n2w_w2n]
QED

Theorem ao_safe_arithmetic_zero_one:
  !x:bytes32.
    safe_div x 0w = 0w /\ safe_div 0w x = 0w /\ safe_div x 1w = x /\
    safe_mod x 0w = 0w /\ safe_mod 0w x = 0w /\ safe_mod x 1w = 0w /\
    safe_sdiv x 0w = 0w /\ safe_sdiv 0w x = 0w /\ safe_sdiv x 1w = x /\
    safe_smod x 0w = 0w /\ safe_smod 0w x = 0w /\ safe_smod x 1w = 0w
Proof
  gen_tac >> Cases_on `x = 0w` >>
  simp[safe_div_def, safe_mod_def, safe_sdiv_def, safe_smod_def,
       wordsTheory.word_div_def, wordsTheory.word_mod_def,
       wordsTheory.word_quot_def, wordsTheory.word_rem_def,
       wordsTheory.word_msb_n2w, bitTheory.BIT_ZERO,
       wordsTheory.WORD_NEG_NEG] >>
  Cases_on `word_msb x` >>
  simp[wordsTheory.word_div_def, wordsTheory.word_mod_def,
       wordsTheory.WORD_NEG_NEG, wordsTheory.w2n_eq_0,
       fcpLib.INDEX_CONV ``dimindex(:256)``, bitTheory.BIT_DEF]
QED

Theorem ao_power_of_two_edges[local]:
  is_power_of_two (1w:bytes32) /\
  passSharedDefs$word_log2 (1w:bytes32) = 0w /\
  is_power_of_two (n2w (2 ** 255):bytes32) /\
  passSharedDefs$word_log2 (n2w (2 ** 255):bytes32) = 255w
Proof
  rpt conj_tac
  >- simp[passSharedDefsTheory.is_power_of_two_def]
  >- (simp[passSharedDefsTheory.word_log2_def] >> EVAL_TAC)
  >- (rewrite_tac[passSharedDefsTheory.is_power_of_two_def] >>
      CONV_TAC wordsLib.WORD_EVAL_CONV)
  >> simp[passSharedDefsTheory.word_log2_def, wordsTheory.w2n_n2w,
          wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >>
     EVAL_TAC
QED

Theorem ao_opt_muldiv_correct:
  !inst s t out.
    (inst.inst_opcode = MUL \/ inst.inst_opcode = Div \/
     inst.inst_opcode = SDIV \/ inst.inst_opcode = Mod \/
     inst.inst_opcode = SMOD) /\
    step_inst_base inst s = OK t /\ MEM out (ao_opt_muldiv inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  (Cases_on `inst.inst_operands` >> gvs[ao_opt_muldiv_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_muldiv_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_muldiv_def] >>
  Cases_on `lit_eq a 0w \/ lit_eq b 0w`
  >- (gvs[ao_opt_muldiv_def] >>
      gvs (local_opcode_eqs [``venomInst$MUL``, ``venomInst$Div``, ``venomInst$SDIV``, ``venomInst$Mod``, ``venomInst$SMOD``, ``venomInst$ASSIGN``]) >>
      gvs[exec_pure2_def, AllCaseEqs()] >>
      gvs[passSharedDefsTheory.lit_eq_def, AllCaseEqs()] >>
      Cases_on `a` >> Cases_on `b` >>
      gvs[eval_operand_def, exec_pure1_def,
          ao_safe_arithmetic_zero_one]) >>
  Cases_on `lit_eq b 1w`
  >- (gvs[ao_opt_muldiv_def] >>
      gvs (local_opcode_eqs [``venomInst$MUL``, ``venomInst$Div``, ``venomInst$SDIV``, ``venomInst$Mod``, ``venomInst$SMOD``, ``venomInst$ASSIGN``]) >>
      gvs[exec_pure2_def, AllCaseEqs()] >>
      Cases_on `b` >>
      gvs[passSharedDefsTheory.lit_eq_def, eval_operand_def,
          exec_pure1_def, ao_safe_arithmetic_zero_one]) >>
  Cases_on `b` >> gvs[ao_opt_muldiv_def, passSharedDefsTheory.lit_eq_def] >>
  rename1 `inst.inst_operands = [a; Lit w]` >>
  Cases_on `is_power_of_two w` >> gvs[] >>
  gvs (local_opcode_eqs [``venomInst$MUL``, ``venomInst$Div``, ``venomInst$SDIV``, ``venomInst$Mod``, ``venomInst$SMOD``,
                         ``SHL``, ``SHR``, ``venomInst$AND``]) >>
  gvs[exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
  simp[ao_power_of_two_mul, ao_power_of_two_div, ao_power_of_two_mod])
QED

Theorem ao_opt_signextend_correct:
  !ra lbl idx inst s t out.
    inst.inst_opcode = SIGNEXTEND /\ step_inst_base inst s = OK t /\
    (!a w. MEM a inst.inst_operands /\ eval_operand a s = SOME w ==>
      in_range (range_get_range ra lbl idx a) w) /\
    MEM out (ao_opt_signextend ra lbl idx inst) ==>
    step_inst_base out s = OK t
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[ao_opt_signextend_def] >>
  rename1 `inst.inst_operands = a::rest` >>
  Cases_on `rest` >> gvs[ao_opt_signextend_def] >>
  rename1 `inst.inst_operands = a::b::tail` >>
  Cases_on `tail` >> gvs[ao_opt_signextend_def] >>
  Cases_on `a` >> gvs[ao_opt_signextend_def] >>
  rename1 `inst.inst_operands = [Lit n;b]` >>
  Cases_on `31w <=+ n`
  >- (gvs[] >> gvs (local_opcode_eqs [``venomInst$SIGNEXTEND``, ``venomInst$ASSIGN``]) >>
      gvs[exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
      simp[exec_pure1_def, ao_sign_extend_large]) >>
  gvs[wordsTheory.WORD_LS, wordsTheory.dimword_def] >>
  Cases_on `vr_is_top (range_get_range ra lbl idx b)` >> gvs[] >>
  Cases_on `vr_lo (range_get_range ra lbl idx b) >=
              -&(2 ** (8 * (w2n n + 1) - 1)) /\
            vr_hi (range_get_range ra lbl idx b) <=
              &(2 ** (8 * (w2n n + 1) - 1)) - 1` >> gvs[] >>
  gvs (local_opcode_eqs [``venomInst$SIGNEXTEND``, ``venomInst$ASSIGN``]) >>
  gvs[exec_pure2_def, eval_operand_def, AllCaseEqs()] >>
  first_x_assum (qspec_then `b` mp_tac) >> simp[] >> strip_tac >>
  `sign_extend n v2 = v2` by
    (`n = n2w (w2n n)` by simp[] >> pop_assum SUBST1_TAC >>
     irule ao_sign_extend_within >>
     Cases_on `range_get_range ra lbl idx b` >>
     gvs[valueRangeDefsTheory.in_range_def,
         valueRangeDefsTheory.vr_is_top_def, valueRangeDefsTheory.vr_lo_def,
         valueRangeDefsTheory.vr_hi_def] >> Cooper.COOPER_TAC) >>
  simp[exec_pure1_def]
QED
