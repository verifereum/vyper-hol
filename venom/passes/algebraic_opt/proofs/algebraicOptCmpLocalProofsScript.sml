Theory algebraicOptCmpLocalProofs
Ancestors
  algebraicOptDefs integer_word valueRangeDefs venomExecSemantics venomState stateFrame
  passSimulationDefs dfgAnalysisProps

Theorem ao_unsigned_gt_complement:
  !x w : bytes32. w <> 0w - 1w ==>
    (x <+ w + 1w <=> ~(w <+ x))
Proof
  rpt strip_tac >>
  qpat_x_assum `w <> _` mp_tac >>
  once_rewrite_tac[GSYM wordsTheory.w2n_11] >>
  CONV_TAC (LAND_CONV (RAND_CONV (RAND_CONV wordsLib.WORD_EVAL_CONV))) >>
  strip_tac >>
  qspec_then `w : bytes32` mp_tac wordsTheory.w2n_lt >>
  simp[wordsTheory.WORD_LO, wordsTheory.word_add_def,
       wordsTheory.w2n_n2w] >>
  strip_tac >> gvs[] >>
  `w2n w + 1 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  simp[arithmeticTheory.LESS_MOD, wordsTheory.dimword_def]
QED

Theorem ao_unsigned_lt_complement:
  !x w : bytes32. w <> 0w ==>
    (w - 1w <+ x <=> ~(x <+ w))
Proof
  rpt strip_tac >>
  `w - 1w <> 0w - 1w` by simp[] >>
  drule ao_unsigned_gt_complement >>
  disch_then (qspec_then `x` mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem ao_signed_gt_complement:
  !x w : bytes32. w <> i2w INT256_MAX ==>
    (x < w + 1w <=> ~(w < x))
Proof
  rpt strip_tac >>
  `w2i w <> INT256_MAX` by metis_tac[integer_wordTheory.i2w_w2i] >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_le >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_ge >>
  `w2i (w + 1w) = w2i w + 1` by
    (`w + 1w = i2w (w2i w + 1)` by
       simp[GSYM integer_wordTheory.word_add_i2w, integer_wordTheory.w2i_1] >>
     pop_assum SUBST1_TAC >> irule integer_wordTheory.w2i_i2w >>
     fs[GSYM INT256_MIN_def, GSYM INT256_MAX_def] >> Omega.OMEGA_TAC) >>
  simp[integer_wordTheory.WORD_LTi] >> Omega.OMEGA_TAC
QED

Theorem ao_signed_lt_complement:
  !x w : bytes32. w <> i2w INT256_MIN ==>
    (w - 1w < x <=> ~(x < w))
Proof
  rpt strip_tac >>
  `w2i w <> INT256_MIN` by metis_tac[integer_wordTheory.i2w_w2i] >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_le >>
  qspec_then `w : bytes32` assume_tac integer_wordTheory.w2i_ge >>
  `w2i (w - 1w) = w2i w - 1` by
    (`w - 1w = i2w (w2i w - 1)` by
       simp[GSYM integer_wordTheory.word_sub_i2w, integer_wordTheory.w2i_1] >>
     pop_assum SUBST1_TAC >> irule integer_wordTheory.w2i_i2w >>
     fs[GSYM INT256_MIN_def, GSYM INT256_MAX_def] >> Omega.OMEGA_TAC) >>
  simp[integer_wordTheory.WORD_LTi] >> Omega.OMEGA_TAC
QED

Theorem ao_cmp_threshold_complement:
  !signed is_gt lo never hi (x : bytes32) w.
    (if signed then ao_signed_boundaries is_gt
     else ao_unsigned_boundaries is_gt) = (lo,never,hi) /\ w <> never ==>
    bool_to_word
      (if signed then (if is_gt then x < w + 1w else w - 1w < x)
       else (if is_gt then x <+ w + 1w else w - 1w <+ x)) =
    bool_to_word
      (bool_to_word
        (if signed then (if is_gt then w < x else x < w)
         else (if is_gt then w <+ x else x <+ w)) = 0w)
Proof
  Cases >> Cases >>
  simp[ao_signed_boundaries_def, ao_unsigned_boundaries_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[ao_signed_gt_complement, SRULE [] ao_signed_lt_complement,
       ao_unsigned_gt_complement, SRULE [] ao_unsigned_lt_complement]
  >~ [`bool_to_word (~(w < x))`] >-
     (Cases_on `w < x` >> simp[bool_to_word_def])
  >~ [`bool_to_word (~(x < w))`] >-
     (Cases_on `x < w` >> simp[bool_to_word_def])
  >~ [`bool_to_word (~(w <+ x))`] >-
     (Cases_on `w <+ x` >> simp[bool_to_word_def])
  >> Cases_on `x <+ w` >> simp[bool_to_word_def]
QED

Theorem ao_cmp_iszero_compensation:
  !fuel ctx inst v out s t b.
    inst.inst_opcode = ISZERO /\ inst.inst_operands = [Var v] /\
    inst.inst_outputs = [out] /\
    lookup_var v s = SOME (bool_to_word b) /\
    lookup_var v t = SOME (bool_to_word (~b)) ==>
    step_inst fuel ctx inst s = OK (update_var out (bool_to_word (~b)) s) /\
    step_inst fuel ctx (inst with inst_opcode := ASSIGN) t =
      OK (update_var out (bool_to_word (~b)) t)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `b` >>
  simp[step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def] >>
  gvs[exec_pure1_def, eval_operand_def, bool_to_word_def]
QED

Theorem ao_cmp_assert_compensation:
  !fuel ctx inst iz v fresh s t b.
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [Var v] /\
    iz.inst_opcode = ISZERO /\ iz.inst_operands = [Var v] /\
    iz.inst_outputs = [fresh] /\
    lookup_var v s = SOME (bool_to_word b) /\
    lookup_var v t = SOME (bool_to_word (~b)) ==>
    ?t1. step_inst fuel ctx iz t = OK t1 /\
      execution_frame t1 = execution_frame t /\
      step_inst fuel ctx inst s =
        (if b then OK s
         else Abort Revert_abort (revert_state (set_returndata [] s))) /\
      step_inst fuel ctx (inst with inst_operands := [Var fresh]) t1 =
        (if b then OK t1
         else Abort Revert_abort (revert_state (set_returndata [] t1)))
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `update_var fresh (bool_to_word b) t` >>
  conj_tac
  >- (Cases_on `b` >> simp[step_inst_non_invoke] >>
      asm_rewrite_tac[step_inst_base_def] >>
      gvs[exec_pure1_def, eval_operand_def, bool_to_word_def]) >>
  conj_tac >- simp[update_var_def] >>
  Cases_on `b` >> simp[step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def] >>
  gvs[eval_operand_def, bool_to_word_def] >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem ao_cmp_producer_refresh:
  !fuel ctx inst op out s t x w signed is_gt lo never hi.
    inst.inst_opcode =
      (if signed then (if is_gt then SGT else SLT)
       else (if is_gt then GT else LT)) /\
    inst.inst_operands = [op; Lit w] /\ inst.inst_outputs = [out] /\
    eval_operand op s = SOME x /\ eval_operand op t = SOME x /\
    (if signed then ao_signed_boundaries is_gt
     else ao_unsigned_boundaries is_gt) = (lo,never,hi) /\ w <> never ==>
    ?b. step_inst fuel ctx inst s = OK (update_var out (bool_to_word b) s) /\
      step_inst fuel ctx
        (inst with <|inst_opcode := flip_comparison_opcode inst.inst_opcode;
                     inst_operands := [op; Lit (if is_gt then w + 1w else w - 1w)]|>) t =
        OK (update_var out (bool_to_word (~b)) t)
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `if signed then (if is_gt then w < x else x < w)
              else (if is_gt then w <+ x else x <+ w)` >>
  drule_all ao_cmp_threshold_complement >>
  disch_then (qspec_then `x` assume_tac) >>
  Cases_on `signed` >> Cases_on `is_gt` >>
  gvs[passSharedDefsTheory.flip_comparison_opcode_def] >>
  simp[step_inst_non_invoke] >> asm_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[venomInstTheory.instruction_accfupds,
                   combinTheory.K_THM, venomInstTheory.opcode_case_def] >>
  simp[exec_pure2_def, eval_operand_def, wordsTheory.WORD_LO,
       integer_wordTheory.WORD_GTi, integer_wordTheory.WORD_LTi] >>
  gvs[integer_wordTheory.WORD_LTi, integerTheory.int_gt] >>
  `!b. bool_to_word (bool_to_word b = (0w : bytes32)) =
       (bool_to_word (~b) : bytes32)` by
    (Cases >> simp[bool_to_word_def]) >>
  gvs[wordsTheory.WORD_LO, arithmeticTheory.GREATER_DEF]
QED

Theorem ao_cmp_iszero_unwritten:
  !fuel ctx inst v out s t.
    inst.inst_opcode = ISZERO /\ inst.inst_operands = [Var v] /\
    inst.inst_outputs = [out] /\ lookup_var v s = NONE /\ lookup_var v t = NONE ==>
    step_inst fuel ctx inst s = Error "undefined operand" /\
    step_inst fuel ctx (inst with inst_opcode := ASSIGN) t =
      Error "undefined operand"
Proof
  rpt gen_tac >> strip_tac >> simp[step_inst_non_invoke] >>
  asm_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[venomInstTheory.instruction_accfupds,
                 combinTheory.K_THM, venomInstTheory.opcode_case_def] >>
  simp[exec_pure1_def, eval_operand_def]
QED

Theorem ao_cmp_singleton_read:
  !fn v consumer inst.
    dfg_get_uses (dfg_build_function fn) v = [consumer] /\
    MEM inst (fn_insts fn) /\ MEM v (operand_vars inst.inst_operands) ==>
    inst = consumer
Proof
  rpt gen_tac >> strip_tac >>
  drule_all dfg_build_function_uses_complete >> simp[]
QED
