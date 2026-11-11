Theory augAssignPtrNumericProbe
Ancestors exprSimArith exprBopSimDefs exprLowering exprLoweringProps
  vyperValue valueEncoding loweringSlice list arithmeticProps builtinMath

(* This is the numerical premise of binop_frag_straight, not a lifted path. *)
Theorem checked_integer_numeric_witness:
  MEM bop [Add; Sub; Mul] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 ==>
  (?v. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
       word_value v /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y ss = SOME (val_to_w256 (IntV i2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
             eval_operand op t = SOME (val_to_w256 v)) \/
  (?m. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
         INR (Error (RuntimeError m)) /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y ss = SOME (val_to_w256 (IntV i2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t)
Proof
  strip_tac >>
  qabbrev_tac `rr = if bop = Add then i1 + i2 else if bop = Sub then i1 - i2 else i1 * i2` >>
  `bop_result cx ann bop tys (IntV i1) (IntV i2) es =
     if within_int_bound u rr then INL (IntV rr)
     else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (qspecl_then [`cx`, `ann`, `bop`] (assume_tac o SRULE [LET_THM])
       bop_result_checked >> fs[MEM, Abbr `rr`]) >>
  Cases_on `within_int_bound u rr` >>
  simp[word_value_def, val_to_w256_def] >>
  rpt strip_tac >> fs[] >> gvs[compile_binop_def, Abbr `rr`]
  >>~- ([`compile_safe_add _ _ _ _ = _`], drule_all compile_safe_add_run >> simp[])
  >>~- ([`compile_safe_sub _ _ _ _ = _`], drule_all compile_safe_sub_run >> simp[]) >>
  drule_all compile_safe_mul_run >> simp[]
QED

Theorem divmod_integer_numeric_witness:
  MEM bop [Div; Mod] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 ==>
  (?v. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
       word_value v /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y ss = SOME (val_to_w256 (IntV i2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = OK t /\
             eval_operand op t = SOME (val_to_w256 v)) \/
  (?m. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
         INR (Error (RuntimeError m)) /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 (IntV i1)) /\
         eval_operand y ss = SOME (val_to_w256 (IntV i2)) ==>
         ?t. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort t)
Proof
  strip_tac >>
  qspecl_then [`ty`, `u`] mp_tac type_to_int_bound_bits >> simp[] >> strip_tac >>
  `math_val ty (i2w i1 : bytes32) = i1 /\ math_val ty (i2w i2 : bytes32) = i2` by
    gvs[math_val_i2w] >>
  `i2 = 0 <=> i2w i2 = (0w : bytes32)` by
    (eq_tac >> strip_tac >- simp[integer_wordTheory.i2w_0] >>
     qspecl_then [`type_bits ty`, `is_signed_type ty`, `i2`] mp_tac
       i2w_eq_0_within >> gvs[]) >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`] (mp_tac o SRULE []) bop_result_divmod >>
  disch_then (qspecl_then [`es`, `i1`, `i2`, `u`] mp_tac) >>
  impl_tac >- fs[MEM] >>
  qmatch_goalsub_abbrev_tac `(BAD ==> _) /\ _ ==> _` >>
  Cases_on `BAD` >> simp[] >> strip_tac
  >- (disj2_tac >> qexists `m` >> simp[val_to_w256_def] >>
      rpt strip_tac >> fs[markerTheory.Abbrev_def] >>
      gvs[compile_binop_def, integer_wordTheory.i2w_0]
      >- metis_tac[compile_safe_div_by_zero]
      >- (gvs[math_val_def] >> irule compile_safe_div_overflow >>
          simp[] >> metis_tac[]) >>
      metis_tac[compile_safe_mod_by_zero]) >>
  qpat_x_assum `_ ==> ?z. _` mp_tac >>
  impl_tac >- fs[markerTheory.Abbrev_def] >>
  strip_tac >>
  rename1 `bop_result _ _ _ _ _ _ _ = INL (IntV result)` >>
  disj1_tac >> qexists `IntV result` >> simp[val_to_w256_def, word_value_def] >>
  rpt strip_tac >> fs[markerTheory.Abbrev_def] >>
  `math_val ty (i2w i1 : bytes32) = i1 /\ math_val ty (i2w i2 : bytes32) = i2` by
    gvs[math_val_i2w] >>
  `in_type_range ty i1` by gvs[in_type_range_within] >>
  gvs[compile_binop_def]
  >- (`is_signed_type ty ==>
         in_type_range ty (w2i (i2w i1 : bytes32)) /\
         ~(w2i (i2w i1 : bytes32) = -&(2 ** (type_bits ty - 1)) /\
           w2i (i2w i2 : bytes32) = -1)` by
        (Cases_on `is_signed_type ty` >> gvs[math_val_def]) >>
      drule_all compile_safe_div_ok >>
      Cases_on `is_signed_type ty` >> simp[]) >>
  drule_all compile_safe_mod_correct >> Cases_on `is_signed_type ty` >> simp[]
QED
