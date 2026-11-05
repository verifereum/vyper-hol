(* Ordinary unary expression simulation composition. *)
Theory exprSimUnop
Ancestors
  exprUnopStraight exprUnopSimDefs exprSimUnopCompose
  exprSimUnopProps
  exprSimProps
  exprSimDefs
  loweringPosts
  arithmetic list integer words integer_word byte
  fragExec varsExt  freshWrites
  exprBopLowering loweringSlice
  exprLowering emitHelper emitHelperProps exprLoweringProps
  builtinSimple builtinProps arithmeticProps vyperArith
  compileEnv vyperAST vyperInterpreter vyperState vyperContext vyperValue
  vyperValueOperation valueEncoding venomExecSemantics venomInst venomState
  vyperTyping vyperTypeSystem
Libs
  intLib pairLib




Theorem compile_not_frag:
  !ctx func cenv cx ann tys v1 es0 tv1.
    (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
     is_flag_type ann) /\
    evaluate_type (get_tenv cx) ann = SOME tv1 /\ value_has_type tv1 v1 /\
    (!nsid m. ann = FlagT nsid /\ tv1 = FlagTV m ==>
              cenv.ce_flag_n_members (nsid_to_string nsid) = m) ==>
    unop_frag ctx func cenv cx
      (\x. if ann = BaseT BoolT then emit_op ISZERO [x]
           else compile_invert x ann cenv)
      (typed_val_to_w256 tv1 v1) ann (unop_result cx ann Not tys v1 es0) es0
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (strip_assume_tac o MATCH_MP not_type_cases)
                              strip_assume_tac) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  irule unop_frag_straight >>
  (conj_tac
   >- (gen_tac >> simp[compile_invert_def, LET_THM] >>
       irule straight_fresh_emit_op >> simp[fresh_write_op_def])) >>
  (conj_tac >- simp[is_word_type_def]) >>
  disch_then kall_tac >> disj1_tac >>
  Cases_on `v1` >>
  gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
      vyperASTTheory.type_to_int_bound_def, typed_val_to_w256_def,
      val_to_w256_def, compile_invert_def, vyperValueTheory.evaluate_type_def]
  >~ [`emit_op ISZERO`]
  >- (rpt strip_tac >> drule_all emit_op_ISZERO_correct_mem >> strip_tac >>
      qexists_tac `ss'` >> asm_rewrite_tac[] >> BasicProvers.every_case_tac >>
      gvs[bool_to_word_def])
  >~ [`i2w _`]
  >- (rename1 `Num i` >> rpt strip_tac >>
      drule_all emit_op_NOT_correct >> rw[] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def])
  >~ [`PAD_RIGHT`]
  >- (rename1 `LENGTH bs = 32` >> rpt strip_tac >> gvs[listTheory.PAD_RIGHT] >>
      drule_all emit_op_NOT_correct >> rw[] >>
      simp[listTheory.PAD_RIGHT, length_word_to_bytes_be,
           word_of_bytes_be_to_bytes]) >>
  rename1 `k < 2 ** m` >> rpt strip_tac >>
  qspecl_then [`XOR`, `word_xor`, `x`, `Lit (n2w (2 ** m - 1))`, `n2w k`,
               `n2w (2 ** m - 1)`, `sa`, `op`, `sb`, `ss`]
    mp_tac emit_op_pure2_correct >>
  impl_tac
  >- (simp[eval_operand_def] >> irule step_XOR >> simp[eval_operand_def]) >>
  rw[] >> simp[flag_not_xor]
QED

Theorem compile_abs_frag:
  !ctx func cenv cx tys v1 es0.
    value_has_type (BaseTV (IntT 256)) v1 ==>
    unop_frag ctx func cenv cx compile_builtin_abs
      (typed_val_to_w256 (BaseTV (IntT 256)) v1) (BaseT (IntT 256))
      (unop_result cx (BaseT (IntT 256)) Abs tys v1 es0) es0
Proof
  rpt strip_tac >> irule unop_frag_straight >>
  rpt conj_tac
  >- simp[straight_fresh_abs]
  >- simp[is_word_type_def] >>
  disch_then kall_tac >>
  Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `within_int_bound _ i` >>
  drule int256_abs_bound >> strip_tac >>
  drule_all abs_i2w >> strip_tac >>
  simp[unop_result_def, evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, bounded_int_op_def,
       typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `i = INT_MIN (:256)`
  >- (`i2w i = (INT_MINw : bytes32)` by metis_tac[] >>
      qpat_x_assum `i = _`
        (fn th => REWRITE_TAC [EQT_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
      disj2_tac >> simp[] >>
      rpt strip_tac >> drule_all compile_builtin_abs_run >> simp[]) >>
  `i2w i <> (INT_MINw : bytes32)` by metis_tac[] >>
  qpat_x_assum `i <> _`
    (fn th => REWRITE_TAC [EQF_INTRO (SIMP_RULE (srw_ss()) [] th)]) >>
  disj1_tac >>
  simp[vyperValueTheory.evaluate_type_def, typed_val_to_w256_def,
       val_to_w256_def] >>
  rpt strip_tac >> drule_all compile_builtin_abs_run >>
  disch_then (drule o CONJUNCT1) >> strip_tac >>
  qexists_tac `ss'` >> asm_rewrite_tac[] >> simp[]
QED


Theorem compile_neg_frag:
  !ctx func cenv cx t tv v es.
    is_numeric_type t /\ ~is_uint_type t /\
    evaluate_type (get_tenv cx) t = SOME tv /\ value_has_type tv v ==>
    unop_frag ctx func cenv cx (\x. compile_neg x t)
      (typed_val_to_w256 tv v) t (unop_result cx t Neg [t] v es) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all neg_typed_source >> disch_then (qspec_then `es` assume_tac) >>
  irule unop_frag_straight >>
  (conj_tac >- (gen_tac >> BETA_TAC >>
    irule (CONV_RULE (DEPTH_CONV ETA_CONV) straight_fresh_neg))) >>
  (conj_tac >- (Cases_on `t` >>
    gvs[is_numeric_type_def, is_int_type_def, is_word_type_def] >>
    rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def])) >>
  disch_then kall_tac >>
  Cases_on `w2i (FST (type_bounds t)) < w2i (typed_val_to_w256 tv v)` >>
  gvs[] >> rpt strip_tac >> drule_all compile_neg_run >> simp[]
QED
