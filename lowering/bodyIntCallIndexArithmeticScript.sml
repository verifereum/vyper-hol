(* Integer interpretation of the emitted array bounds check. *)
Theory bodyIntCallIndexArithmetic
Ancestors
  exprSimArrayIndex arithmeticProps integer_word words integer arithmetic
  exprSimArith vyperTypeSystem vyperValue vyperTyping valueEncoding compileEnv
  loweringPosts vyperTypeStatePreservation venomState vyperState vyperArray
  vyperValueOperation alist typedMemoryCopy

Theorem idx_in_range_math_val:
  cnt < dimword (:256) ==>
  (idx_in_range (is_signed_type ty) (i:bytes32) (n2w cnt) <=>
   0 <= math_val ty i /\ math_val ty i < &cnt)
Proof
  strip_tac >>
  simp[idx_in_range_def, math_val_def, WORD_LTi, word_0_w2i] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  simp[w2i_eq_w2n] >>
  Cases_on `w2n i < INT_MIN (:256)` >> simp[] >>
  mp_tac (Q.ISPEC `i:bytes32` w2n_lt) >> intLib.ARITH_TAC
QED

Theorem typed_integer_word_math_val:
  is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv (IntV n) ==>
  math_val ty (typed_val_to_w256 tv (IntV n)) = n
Proof
  Cases_on `ty` >> simp[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  simp[evaluate_type_def, AllCaseEqs(), value_has_type_def,
       typed_val_to_w256_def, val_to_w256_def] >> rpt strip_tac >>
  gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  irule math_val_i2w >>
  simp[type_bits_def, is_signed_type_def, within_int_bound_def]
QED

Theorem typed_index_operand_bounds:
  is_int_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ expr_val_rel cx ty v op s /\ cnt < dimword (:256) ==>
  ?n w. v = IntV n /\ eval_operand op s = SOME w /\ math_val ty w = n /\
    (idx_in_range (is_signed_type ty) w (n2w cnt) <=> 0 <= n /\ n < &cnt)
Proof
  strip_tac >> drule_all int_typed_value_is_IntV >> strip_tac >> gvs[] >>
  `is_word_type ty` by
    (Cases_on `ty` >> gvs[is_int_type_def] >>
     rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
     gvs[is_int_type_def, is_word_type_def]) >>
  fs[expr_val_rel_def] >>
  `w = typed_val_to_w256 tv (IntV i)` by metis_tac[] >>
  `math_val ty w = i` by metis_tac[typed_integer_word_math_val] >>
  metis_tac[idx_in_range_math_val]
QED

Theorem typed_fixed_array_selection:
  value_has_type (ArrayTV et (Fixed cnt)) a ==>
  if 0 <= n /\ n < &cnt then
    ?v. evaluate_subscripts (ArrayTV et (Fixed cnt)) a [ValueSubscript (IntV n)] = INL v /\
        mem_path_offset (ArrayTV et (Fixed cnt)) [ValueSubscript (IntV n)] =
          SOME (Num n * type_memory_size et,et)
  else evaluate_subscripts (ArrayTV et (Fixed cnt)) a [ValueSubscript (IntV n)] =
         INR (RuntimeError "evaluate_subscripts array_index")
Proof
  Cases_on `n` >> simp[] >>
  Cases_on `a` >> simp[value_has_type_def] >>
  rename1 `value_has_type (ArrayTV et (Fixed cnt)) (ArrayV av)` >>
  Cases_on `av` >> simp[value_has_type_def] >> strip_tac >>
  rw[evaluate_subscripts_def, array_index_sarray, mem_path_offset_def,
     mem_step_offset_def] >>
  simp[AllCaseEqs()] >> metis_tac[optionTheory.option_CASES]
QED

Theorem nonnegative_math_val_w2n:
  0 <= math_val ty (i:bytes32) ==> w2n i = Num (math_val ty i)
Proof
  simp[math_val_def] >> Cases_on `is_signed_type ty` >> simp[] >>
  simp[w2i_eq_w2n] >> Cases_on `w2n i < INT_MIN (:256)` >> simp[] >>
  mp_tac (Q.ISPEC `i:bytes32` w2n_lt) >> intLib.ARITH_TAC
QED

Theorem index_address_nonwrapping:
  math_val ty (i:bytes32) = n /\ 0 <= n /\
  w2n (b:bytes32) + Num n * sz < dimword (:256) ==>
  w2n (b + i * n2w sz) = w2n b + Num n * sz
Proof
  strip_tac >>
  `w2n i = Num n` by metis_tac[nonnegative_math_val_w2n] >>
  `i = n2w (Num n)` by metis_tac[n2w_w2n] >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[word_mul_n2w] >>
  irule typed_copy_offset_nonwrap >> simp[]
QED
