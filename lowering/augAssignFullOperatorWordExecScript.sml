Theory augAssignFullOperatorWordExec
Ancestors
  bodyBinopFamiliesMemory exprSimBinopFrag exprSimArith exprSimCompare exprBopBitwise
  exprSimHypsDefs exprBopShift exprBopSimDefs exprSimDefs exprBopLowering
  builtinProps arithmeticProps valueEncodingProofs valueEncodingBitwise
  vyperTypeSystem vyperValue vyperTyping vyperValueOperation
  vyperAST valueEncoding exprLowering exprSimProps loweringSlice
  venomExecSemantics venomInst venomState
  compileEnv freshWrites emitHelperProps integer_word words
Libs
  intLib pairLib

Theorem augassign_unsafe_execution:
  !cx bop ann t1 t2 bl el tys v1 v2 es tenv tv1 tv2 x y sa sb op s.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
    expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
    compile_binop bop x y t1 bl el sa = (op,sb) /\
    fresh_vars_wrt sa s /\
    eval_operand x s = SOME (val_to_w256 v1) /\
    eval_operand y s = SOME (val_to_w256 v2) ==>
    (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
    (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_int_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tv2 = tv1` SUBST_ALL_TAC >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ann`, `v1`, `v2`, `es`, `i'`, `i`,
               `type_bits ann`] mp_tac bop_result_unsafe >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_binop_unsafe] >> strip_tac >>
  irule compile_unsafe_binop_correct >>
  goal_assum (drule_at (Pat `compile_unsafe_binop`)) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule step_unsafe_opcode >> asm_rewrite_tac[]
QED

Theorem augassign_shift_execution:
  !cx bop ann t1 t2 bl el tys v1 v2 es tenv tv1 tv2 x y sa sb op s.
    (bop = ShL \/ bop = ShR) /\ well_typed_binop ann bop t1 t2 /\
    word_value_type t1 /\ (?i. v2 = IntV i /\ 0 <= i) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
    expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
    compile_binop bop x y t1 bl el sa = (op,sb) /\
    fresh_vars_wrt sa s /\
    eval_operand x s = SOME (val_to_w256 v1) /\
    eval_operand y s = SOME (val_to_w256 v2) ==>
    (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
    (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?v. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    val_to_w256 v =
      if bop = ShL then word_lsl (val_to_w256 v1) (w2n (val_to_w256 v2))
      else if is_signed_type t1
      then word_asr (val_to_w256 v1) (w2n (val_to_w256 v2))
      else word_lsr (val_to_w256 v1) (w2n (val_to_w256 v2))` by
    (qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` kall_tac >>
     `ann = t1 /\ is_int_type t1 /\ is_int_type t2` by
       (gvs[well_typed_binop_def, word_value_type_def]) >>
     qpat_x_assum `ann = t1` SUBST_ALL_TAC >>
     qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac int_type_value >>
     qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     qpat_x_assum `v1 = IntV _` SUBST_ALL_TAC >>
     qpat_x_assum `v2 = IntV _` SUBST_ALL_TAC >>
     `0 <= i` by metis_tac[vyperValueTheory.value_11] >>
     `within_int_bound (Unsigned 256) i` by
       (Cases_on `is_signed_type t2` >> fs[] >>
        metis_tac[within_int_bound_unsigned_256]) >>
     Cases_on `bop = ShL`
     >- (`type_bits t1 = 256` by gvs[well_typed_binop_def, type_bits_def] >>
         qspecl_then [`cx`, `t1`, `ShL`, `t1`] mp_tac bop_result_shift >>
         simp[] >> disch_then irule >> metis_tac[]) >>
     gvs[] >>
     qspecl_then [`cx`, `t1`, `t1`] mp_tac bop_result_shr >>
     simp[] >> disch_then irule >> metis_tac[]) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  drule_all compile_shift_run >> simp[]
QED

Theorem augassign_rest_execution:
  !cx bop ann t1 t2 bl el tys v1 v2 es tenv tv1 tv2 x y sa sb op s.
    MEM bop [And; Or; XOr; Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
    expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
    compile_binop bop x y t1 bl el sa = (op,sb) /\
    fresh_vars_wrt sa s /\
    eval_operand x s = SOME (val_to_w256 v1) /\
    eval_operand y s = SOME (val_to_w256 v2) ==>
    (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
    (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `t2 = t1` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t2 = t1` SUBST_ALL_TAC >>
  `tv2 = tv1` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `tv2 = tv1` SUBST_ALL_TAC >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (`ann = t1` by gvs[well_typed_binop_def] >>
      qpat_x_assum `ann = t1` SUBST_ALL_TAC >>
      `word_value v1 /\
       (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
         within_int_bound
           (case type_to_int_bound t1 of SOME u => u | NONE => Unsigned 0) i1 /\
         within_int_bound
           (case type_to_int_bound t1 of SOME u => u | NONE => Unsigned 0) i2)` by
        (qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac word_value_type_value_cases >>
         qspecl_then [`tenv`, `t1`, `tv1`, `v2`] mp_tac word_value_type_value_cases >>
         asm_rewrite_tac[] >> rpt strip_tac >>
         gvs[type_to_int_bound_def, word_value_def]) >>
      drule_all bop_result_bitwise >> strip_tac >>
      disj1_tac >> qexists_tac `v` >> simp[] >>
      drule_all compile_bitwise_run >> simp[]) >>
  `word_value v1 /\ (is_uint256 t1 <=> tv1 = BaseTV (UintT 256)) /\
   !m. tv1 = BaseTV (UintT m) \/ tv1 = BaseTV (IntT m) \/ tv1 = FlagTV m ==>
       m <= 256` by
    (qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac word_value_type_value_cases >>
     asm_rewrite_tac[] >> rpt strip_tac >> gvs[word_value_def, is_uint256_def]) >>
  Cases_on `bop = Min \/ bop = Max`
  >- (drule_all bop_result_minmax >> strip_tac >>
      disj1_tac >> qexists_tac `v` >> simp[] >>
      drule_all compile_minmax_correct >> simp[]) >>
  `MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE]` by (Cases_on `bop` >> fs[]) >>
  drule_all bop_result_compare >> strip_tac >>
  `compile_compare bop x y t1 sa = (op,sb)` by
    (qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE]` mp_tac >>
     rw[compile_binop_def] >> gvs[]) >>
  drule_all compile_compare_correct >> strip_tac >>
  disj1_tac >> goal_assum (drule_at Any) >>
  simp[word_value_def, val_to_w256_def] >>
  Cases_on `eval_compare bop t1 (val_to_w256 v1) (val_to_w256 v2)` >>
  simp[bool_to_word_def]
QED
