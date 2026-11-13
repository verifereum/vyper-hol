(* Ordinary integer result-clamp execution for extract32. *)
Theory bodyMemTbExtract32IntClamp
Ancestors
  convertScalarBytesRun exprSimArith exprLowering exprLoweringProps
  compileEnv emitHelperProps venomState words integer_word
  vyperValueOperation valueEncoding list rich_list

Theorem extract32_int_clamp_ok:
  compile_clamp_basetype x (if sg then BaseT (IntT b) else BaseT (UintT b))
    sa = (op,sb) /\
  eval_operand x s = SOME w /\ fresh_vars_wrt sa s /\ b <= 256 /\
  in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
    (if sg then w2i w else &(w2n w)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME w
Proof
  strip_tac >> Cases_on `b < 256`
  >- (`compile_int_clamp sg b x sa = (op,sb)` by
        (Cases_on `sg` >> gvs[compile_clamp_basetype_def, scalar_int_clamp_eq]) >>
      drule_all scalar_int_clamp_word_ok >> simp[]) >>
  Cases_on `sg` >> gvs[compile_clamp_basetype_def, comp_return_def] >>
  simp[emitted_insts_def, run_inst_seq_def]
QED

Theorem extract32_int_clamp_narrow_abort[local]:
  compile_clamp_basetype x (if sg then BaseT (IntT b) else BaseT (UintT b))
    sa = (op,sb) /\
  eval_operand x s = SOME w /\ fresh_vars_wrt sa s /\ b < 256 /\
  ~in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
    (if sg then w2i w else &(w2n w)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >>
  `compile_int_clamp sg b x sa = (op,sb)` by
    (Cases_on `sg` >> gvs[compile_clamp_basetype_def, scalar_int_clamp_eq]) >>
  `b <= 256` by decide_tac >> drule_all scalar_int_clamp_word_abort >> simp[]
QED

Theorem extract32_int_word_full_range[local]:
  in_type_range (if sg then BaseT (IntT 256) else BaseT (UintT 256))
    (if sg then w2i (w:bytes32) else &(w2n w))
Proof
  Cases_on `sg` >> simp[arithmeticPropsTheory.in_type_range_def,
    type_bits_def, is_signed_type_def]
  >- (qspec_then `w` mp_tac (GEN_ALL w2i_le) >>
      qspec_then `w` mp_tac (GEN_ALL w2i_ge) >>
      simp[INT_MIN_def, INT_MAX_def, wordsTheory.INT_MIN_def, dimword_def] >>
      intLib.ARITH_TAC) >>
  qspec_then `w` mp_tac (GEN_ALL w2n_lt) >> simp[dimword_def]
QED

Theorem extract32_int_clamp_abort:
  compile_clamp_basetype x (if sg then BaseT (IntT b) else BaseT (UintT b))
    sa = (op,sb) /\
  eval_operand x s = SOME w /\ fresh_vars_wrt sa s /\ b <= 256 /\
  ~in_type_range (if sg then BaseT (IntT b) else BaseT (UintT b))
    (if sg then w2i w else &(w2n w)) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t
Proof
  strip_tac >> Cases_on `b = 256`
  >- metis_tac[extract32_int_word_full_range] >>
  `b < 256` by decide_tac >> drule_all extract32_int_clamp_narrow_abort >> simp[]
QED
