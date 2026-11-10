Theory convertScalarFlags
Ancestors
  exprUnopStraight
  convertScalarBytesRun convertScalarProps convertScalarTyping exprSimConvert exprSimUnop
  exprLowering compileEnv vyperValueOperation valueEncoding vyperValue
  venomExecSemantics exprLoweringProps integer_word arithmeticProps
Libs
  intLib

Theorem scalar_flag_int_result_frag:
  !ctx func cenv cx nsid m sg b es0.
    m < 2 ** 256 /\ 0 < b /\ (sg ==> 1 < b) /\ b <= 256 ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvIntToInt F 256 sg b))
      (typed_val_to_w256 (FlagTV n) (FlagV m))
      (BaseT (if sg then IntT b else UintT b))
      (convert_result cx (FlagT nsid)
        (BaseT (if sg then IntT b else UintT b)) (FlagV m)) es0
Proof
  rpt strip_tac >>
  `within_int_bound (Unsigned 256) (&m)` by
    simp[within_int_bound_ineq] >>
  Cases_on `within_int_bound (if sg then Signed b else Unsigned b) (&m)`
  >- (Cases_on `sg` >>
      fs[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
      irule unop_frag_straight >>
      simp[straight_fresh_convert, is_word_type_def] >> strip_tac >>
      qexists_tac `i2w (&m)` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      rpt strip_tac >> drule convert_int_run >>
      disch_then (qspecl_then [`&m`, `ss`] mp_tac) >> simp[i2w_pos, typed_val_to_w256_def, val_to_w256_def]) >>
  Cases_on `sg` >>
  fs[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert, is_word_type_def] >>
  strip_tac >> rpt strip_tac >> drule convert_int_run >>
      disch_then (qspecl_then [`&m`, `ss`] mp_tac) >> simp[i2w_pos, typed_val_to_w256_def, val_to_w256_def]
QED

Theorem scalar_to_flag_run_ok:
  !x n st op st' ss i.
    compile_type_convert x (ConvToFlag n) st = (op,st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss /\
    within_int_bound (Unsigned 256) i /\ Num i < 2 ** n ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
      eval_operand op ss' = SOME (i2w i)
Proof
  rpt strip_tac >> Cases_on `n < 256`
  >- (gvs[compile_type_convert_def] >>
      irule scalar_int_clamp_word_ok >>
      simp[] >> qexistsl_tac [`n`, `F`, `x`] >>
      simp[in_type_range_def, type_bounds_def, type_bits_def,
           is_signed_type_def] >>
      `0 <= i /\ i < &(2 ** 256)` by
        gvs[within_int_bound_ineq] >>
      `Num i < 2 ** 256` by intLib.ARITH_TAC >>
      `i = &Num i` by intLib.ARITH_TAC >>
      qpat_x_assum `i = &Num i` SUBST1_TAC >>
      fs[i2w_pos, wordsTheory.w2n_n2w, wordsTheory.dimword_def]) >>
  gvs[compile_type_convert_def, comp_return_def,
      emitted_insts_refl, run_inst_seq_nil]
QED

Theorem scalar_to_flag_run_abort:
  !x n st op st' ss i.
    compile_type_convert x (ConvToFlag n) st = (op,st') /\
    eval_operand x ss = SOME (i2w i) /\ fresh_vars_wrt st ss /\
    within_int_bound (Unsigned 256) i /\ ~(Num i < 2 ** n) ==>
    ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  `0 <= i /\ i < &(2 ** 256)` by gvs[within_int_bound_ineq] >>
  `Num i < 2 ** 256` by intLib.ARITH_TAC >>
  `n < 256` by
    (spose_not_then assume_tac >>
     `2 ** 256 <= 2 ** n` by simp[] >> decide_tac) >>
  gvs[compile_type_convert_def] >>
  irule scalar_int_clamp_word_abort >> simp[] >>
  qexistsl_tac [`n`, `op`, `F`, `i2w i`, `x`] >>
  simp[in_type_range_def, type_bounds_def, type_bits_def, is_signed_type_def] >>
  `i = &Num i` by intLib.ARITH_TAC >>
  qpat_x_assum `i = &Num i` SUBST1_TAC >>
  fs[i2w_pos, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem scalar_to_flag_result_frag:
  !ctx func cenv cx nsid n i es0.
    FLOOKUP (get_tenv cx) nsid = SOME (FlagArgs n) /\
    within_int_bound (Unsigned 256) i ==>
    unop_frag ctx func cenv cx
      (\x. compile_type_convert x (ConvToFlag n))
      (i2w i) (FlagT nsid)
      (convert_result cx (BaseT (UintT 256)) (FlagT nsid) (IntV i)) es0
Proof
  rpt strip_tac >>
  `0 <= i` by gvs[within_int_bound_ineq] >>
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def] >>
  irule unop_frag_straight >>
  simp[straight_fresh_convert_scalar, is_word_type_def] >>
  Cases_on `Num i < 2 ** n` >> simp[]
  >- (strip_tac >> qexists_tac `i2w i` >>
      simp[evaluate_type_def, typed_val_to_w256_def, val_to_w256_def] >>
      conj_tac
      >- (`i = &Num i` by intLib.ARITH_TAC >>
          qpat_x_assum `i = &Num i` SUBST1_TAC >> simp[i2w_pos]) >>
      rpt strip_tac >> drule_all scalar_to_flag_run_ok >> simp[]) >>
  strip_tac >> rpt strip_tac >> drule_all scalar_to_flag_run_abort >> simp[]
QED
