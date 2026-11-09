Theory augAssignPtrShiftPowerNumeric
Ancestors exprSimBinopFrag exprBopShift exprBopSimDefs exprLowering
  exprLoweringProps valueEncoding vyperTypeSystem vyperValue vyperTyping
  integer words intBits list compileEnv loweringSlice

Theorem shift_typed_numeric_witness:
  MEM bop [ShL; ShR] /\ (?i. v2 = IntV i /\ 0 <= i) /\
  well_typed_binop ann bop t1 t2 /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
  ?v. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      !x y sa sb op ss.
        compile_binop bop x y t1 bl el sa = (op,sb) /\
        fresh_vars_wrt sa ss /\
        eval_operand x ss = SOME (val_to_w256 v1) /\
        eval_operand y ss = SOME (val_to_w256 v2) ==>
        ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
            eval_operand op t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `t1 = ann /\ is_int_type ann /\ is_int_type t2` by
    (Cases_on `bop = ShL` >> gvs[well_typed_binop_def]) >>
  gnvs[] >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`tenv`, `t2`, `tv2`, `IntV i`] mp_tac int_type_value >>
  (impl_tac >- simp[]) >> strip_tac >>
  gnvs[] >>
  `within_int_bound (Unsigned 256) i` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  `?v. bop_result cx ann bop tys (IntV i') (IntV i) es = INL v /\
       word_value v /\ val_to_w256 v =
       (if bop = ShL then word_lsl (val_to_w256 (IntV i')) (w2n (val_to_w256 (IntV i)))
        else if is_signed_type ann
        then word_asr (val_to_w256 (IntV i')) (w2n (val_to_w256 (IntV i)))
        else word_lsr (val_to_w256 (IntV i')) (w2n (val_to_w256 (IntV i))))` by
    (Cases_on `bop = ShL`
     >- (`type_bits ann = 256` by
           gvs[well_typed_binop_def, type_bits_def] >>
         fs[] >> drule_at (Pat `type_to_int_bound _ = _`) bop_result_shift >>
         metis_tac[])
     >> gvs[] >> irule bop_result_shr >> simp[] >>
        qexists `type_bits ann` >> simp[]) >>
  qexists `v` >> simp[] >> rpt strip_tac >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) compile_shift_run >>
  disch_then drule_all >> simp[]
QED

Theorem pow_typed_numeric_witness:
  well_typed_binop ann Exp t1 t2 /\
  (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
  (!n. bl = SOME n ==> v1 = IntV n) /\
  (!n. el = SOME n ==> v2 = IntV n) /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
  ((?v. bop_result cx ann Exp tys v1 v2 es = INL v /\ word_value v /\
      !x y sa sb op ss.
        compile_binop Exp x y t1 bl el sa = (op,sb) /\
        fresh_vars_wrt sa ss /\
        eval_operand x ss = SOME (val_to_w256 v1) /\
        eval_operand y ss = SOME (val_to_w256 v2) ==>
        ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
            eval_operand op t = SOME (val_to_w256 v)) \/
   (?m. bop_result cx ann Exp tys v1 v2 es = INR (Error (RuntimeError m)) /\
      !x y sa sb op ss.
        compile_binop Exp x y t1 bl el sa = (op,sb) /\
        fresh_vars_wrt sa ss /\
        eval_operand x ss = SOME (val_to_w256 v1) /\
        eval_operand y ss = SOME (val_to_w256 v2) ==>
        ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t))
Proof
  disch_tac >>
  `is_int_type t1 /\ is_int_type t2` by gvs[well_typed_binop_def] >>
  qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac int_type_value >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  (impl_tac >- gvs[]) >> strip_tac >> gnvs[well_typed_binop_def] >>
  rename1 `bop_result cx ann Exp tys (IntV a) (IntV b) es` >>
  `type_bits ann MOD 8 = 0` by metis_tac[int_type_byte_width] >>
  drule_then assume_tac bop_result_power >>
  Cases_on `b < 0`
  >- (simp[] >> rpt strip_tac >>
      gvs[compile_binop_def, val_to_w256_def] >>
      drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >>
      simp[] >> `~(0 <= b)` by intLib.ARITH_TAC >> metis_tac[]) >>
  Cases_on `within_int_bound
    (if is_signed_type ann then Signed (type_bits ann) else Unsigned (type_bits ann))
    (a ** Num b)`
  >- (simp[word_value_def] >> rpt strip_tac >>
      gvs[compile_binop_def, val_to_w256_def] >>
      drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >>
      simp[] >> `0 <= b` by intLib.ARITH_TAC >> metis_tac[]) >>
  simp[] >> rpt strip_tac >> gvs[compile_binop_def, val_to_w256_def] >>
  drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >>
  simp[] >> metis_tac[]
QED
