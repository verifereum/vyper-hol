Theory augAssignPtrTypedNumeric
Ancestors augAssignPtrNumericProbe augAssignPtrDecimalNumeric
  augAssignPtrTotalNumeric augAssignPtrShiftPowerNumeric exprSimBinopFrag
  vyperTypeSystem compileEnv list

Theorem binop_typed_numeric_witness:
  well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
  (bop = Exp ==>
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n)) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  word_value_type t1 /\ word_value_type t2 /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  bop <> In /\ bop <> NotIn /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) ==>
  ((?v. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
      !x y sa sb op ss.
        compile_binop bop x y t1 bl el sa = (op,sb) /\
        fresh_vars_wrt sa ss /\
        eval_operand x ss = SOME (val_to_w256 v1) /\
        eval_operand y ss = SOME (val_to_w256 v2) ==>
        ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
            eval_operand op t = SOME (val_to_w256 v)) \/
   (?m. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
      !x y sa sb op ss.
        compile_binop bop x y t1 bl el sa = (op,sb) /\
        fresh_vars_wrt sa ss /\
        eval_operand x ss = SOME (val_to_w256 v1) /\
        eval_operand y ss = SOME (val_to_w256 v2) ==>
        ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t))
Proof
  strip_tac >>
  Cases_on `MEM bop [Add; Sub; Mul; Div; Mod]`
  >- (`t1 = ann /\ t2 = ann /\ is_numeric_type ann` by
        (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
      gnvs[] >>
      Cases_on `is_int_type ann`
      >- (qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
          (impl_tac >- simp[]) >> strip_tac >>
          qspecl_then [`tenv`, `ann`, `tv1`, `v2`] mp_tac int_type_value >>
          (impl_tac >- simp[]) >> strip_tac >> gnvs[] >>
          Cases_on `MEM bop [Add; Sub; Mul]`
          >- (irule checked_integer_numeric_witness >> simp[]) >>
          irule divmod_integer_numeric_witness >> fs[MEM]) >>
      `ann = BaseT DecimalT` by fs[is_numeric_type_def] >> gnvs[] >>
      qspecl_then [`tenv`, `tv1`, `v1`] mp_tac decimal_type_value >>
      (impl_tac >- simp[]) >> strip_tac >>
      qspecl_then [`tenv`, `tv1`, `v2`] mp_tac decimal_type_value >>
      (impl_tac >- simp[]) >> strip_tac >> gnvs[] >>
      Cases_on `MEM bop [Add; Sub; Mod]`
      >- (irule decimal_add_sub_mod_numeric_witness >> simp[]) >>
      irule decimal_mul_div_numeric_witness >> fs[MEM]) >>
  Cases_on `bop = Exp`
  >- (gvs[] >> irule pow_typed_numeric_witness >> simp[] >>
      qexistsl [`t2`, `tenv`, `tv1`, `tv2`] >> simp[]) >>
  Cases_on `bop = ShL \/ bop = ShR`
  >- (disj1_tac >> irule shift_typed_numeric_witness >> simp[MEM] >>
      (conj_tac >- metis_tac[]) >>
      qexistsl [`t2`, `tenv`, `tv1`, `tv2`] >> simp[]) >>
  Cases_on `MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]`
  >- (`t1 = ann /\ t2 = ann /\ is_int_type ann` by
        (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
      gnvs[] >> disj1_tac >> irule unsafe_typed_numeric_witness >>
      simp[] >> qexistsl [`tenv`, `tv1`] >> simp[]) >>
  Cases_on `MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max]`
  >- (`t2 = t1` by
        (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
      gnvs[] >> disj1_tac >> irule compare_typed_numeric_witness >>
      simp[] >> qexistsl [`tenv`, `tv1`] >> simp[]) >>
  `bop = And \/ bop = Or \/ bop = XOr` by
    (Cases_on `bop` >> gvs[well_typed_binop_def]) >>
  `t1 = ann /\ t2 = ann` by
    (Cases_on `bop` >> gvs[well_typed_binop_def]) >>
  gnvs[] >> disj1_tac >> irule bitwise_typed_numeric_witness >> simp[] >>
  qexistsl [`tenv`, `tv1`] >> simp[]
QED
