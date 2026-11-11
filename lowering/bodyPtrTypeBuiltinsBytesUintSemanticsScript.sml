(* Unsigned Convert semantic runs: decoded loader followed by optional clamp. *)
Theory bodyPtrTypeBuiltinsBytesUintSemantics
Ancestors bodyPtrTypeBuiltinsUnsignedSemantics bodyPtrTypeBuiltinsUintClampSemantics
  exprSimConvert exprLowering exprLoweringProps emitHelperProps compileEnv
  fragExec venomState words valueEncoding valueEncodingDefs vyperValue vyperTypeSystem
  vyperTyping vyperValueOperation valueEncodingProofs builtinConvertPrefix

Theorem bytes_uint_conversion_result:
  LENGTH bs <= 32 ==>
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) (BytesV bs) =
  if within_int_bound (Unsigned b)
       (&(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)))))
  then INL (IntV (&(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs))))))
  else INR (Error (RuntimeError "convert BytesV uint bound"))
Proof
  strip_tac >>
  gvs[convert_result_def, evaluate_convert_from_def, evaluate_convert_def,
      unsigned_payload_padding] >> IF_CASES_TAC >> simp[]
QED

Theorem bytes_uint_payload_fits:
  LENGTH bs <= n /\ n <= 32 /\ 8*n <= b ==>
  within_int_bound (Unsigned b)
    (&(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)))))
Proof
  strip_tac >>
  `LENGTH bs <= 32` by decide_tac >>
  drule unsigned_payload_bound >> strip_tac >>
  `2 ** (8*LENGTH bs) <= 2 ** b` by
    (simp[arithmeticTheory.EXP_BASE_LE_MONO] >> decide_tac) >>
  simp[within_int_bound_def] >> decide_tac
QED

Theorem bytes_uint_raw_exact:
  compile_type_convert v (ConvBytestringToInt F b n) sa = (r,sb) /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= n /\ n <= 32 /\ 0 < b /\ b <= 256 /\
  w2n (a+32w) = w2n a+32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs ==>
  if within_int_bound (Unsigned b)
       (&(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)))))
  then ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
    eval_operand r sf = SOME
      (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs))) /\
    fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
    sf.vs_allocas = ss.vs_allocas /\
    (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp_tac pure_ss [compile_type_convert_def, comp_bind_def,
                   comp_return_def, LET_THM, COND_CLAUSES] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `load_bytestring_as_word v SHR sa = ((shifted,k),s1)` >>
  `LENGTH bs <= 32` by decide_tac >>
  drule_all unsigned_load_word_decoded_exact >>
  disch_then (qx_choose_then `t1` strip_assume_tac) >>
  `inst_extends sa s1` by metis_tac[inst_extends_load_bytestring_as_word] >>
  Cases_on `8*n > b` >> gvs[]
  >- (`b <= 256` by decide_tac >> drule_all uint_clamp_exact >>
      qmatch_goalsub_abbrev_tac `if bounded then _ else _` >>
      Cases_on `bounded` >> simp[] >> strip_tac
      >- (qexists_tac `sf` >> simp[] >>
          irule run_inst_seq_compose_ok >> qexistsl_tac [`t1`,`s1`] >>
          metis_tac[inst_extends_compile_int_clamp]) >>
      `inst_extends s1 sb` by metis_tac[inst_extends_compile_int_clamp] >>
      drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]) >>
  `within_int_bound (Unsigned b)
    (&(w2n (word_lsr (word_of_bytes_be bs:bytes32) (8*(32-LENGTH bs)))))` by
    (irule bytes_uint_payload_fits >> qexists_tac `n` >> simp[]) >>
  gvs[comp_return_def] >> qexists_tac `t1` >> simp[]
QED

Theorem bytes_uint_integer_exact:
  compile_type_convert v (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (r,sb) /\
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) (BytesV bs) = res /\
  eval_operand v ss = SOME a /\ fresh_vars_wrt sa ss /\
  LENGTH bs <= n /\ n <= 32 /\ 0 < b /\ b <= 256 /\
  w2n (a+32w) = w2n a+32 /\
  mem_word_at (w2n a) ss.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (w2n a+32) (LENGTH bs) ss.vs_memory = bs ==>
  case res of
  | INL vout => ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 (BaseTV (UintT b)) vout) /\
      fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
      sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  `LENGTH bs <= 32` by decide_tac >>
  qpat_x_assum `compile_type_convert _ _ _ = _` mp_tac >>
  simp[mk_convert_op_def, is_bytestring_type_def] >> disch_tac >>
  drule_all bytes_uint_raw_exact >>
  qpat_x_assum `convert_result _ _ _ _ = _` mp_tac >>
  simp[bytes_uint_conversion_result] >>
  qmatch_goalsub_abbrev_tac `within_int_bound bound i` >>
  Cases_on `within_int_bound bound i` >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[typed_val_to_w256_def, val_to_w256_def, Abbr `i`,
       integer_wordTheory.i2w_pos] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem bytes_uint_semantic_run:
  valid_conversion (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) /\
  well_formed_type tenv (BaseT (UintT b)) /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = SOME stv /\
  value_has_type stv v /\
  convert_result cx (BaseT (BytesT (Dynamic n))) (BaseT (UintT b)) v = res /\
  compile_type_convert op (mk_convert_op (BaseT (BytesT (Dynamic n)))
    (BaseT (UintT b))) sa = (r,sb) /\
  fresh_vars_wrt sa ss /\ eval_operand op ss = SOME a /\
  w2n a+32 < dimword(:256) /\ val_in_memory stv v (w2n a) ss.vs_memory ==>
  case res of
  | INL vout => ?dtv sf. evaluate_type (get_tenv cx) (BaseT (UintT b)) = SOME dtv /\
      run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME (typed_val_to_w256 dtv vout) /\
      fresh_vars_wrt sb sf /\ sf.vs_memory = ss.vs_memory /\
      sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  | INR ex => (?m. ex = Error (RuntimeError m)) /\
      ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, well_formed_type_def,
      valid_conversion_def] >>
  Cases_on `v` >> gvs[value_has_type_def, val_in_memory_def] >>
  `w2n (a+32w) = w2n a+32` by
    simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
         arithmeticTheory.LESS_MOD] >>
  rename1 `mem_bytes_at _ _ _ = bs` >>
  irule bytes_uint_integer_exact >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`bs`,`cx`,`n`,`op`] >> simp[]
QED
