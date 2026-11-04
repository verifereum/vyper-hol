Theory sourceConstBuiltinProps
Ancestors
  sourceConstEval sourceConstBuiltin integer arithmetic
Libs
  intLib ratLib

val () = ratLib.deprecate_rat ();

Theorem source_const_bytes_type_value_ok:
  source_const_bytes_type fixed arg = SC_Value v ==> source_const_value_ok v
Proof
  Cases_on `arg` >> simp[source_const_bytes_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[source_const_value_ok_def]
QED

Theorem source_const_builtin_result_success:
  source_const_builtin_result builtin result = SC_Value v <=> result = SC_Value v
Proof
  Cases_on `result` >> simp[source_const_builtin_result_def] >> rw[]
QED

Theorem source_const_checked_builtin_value_ok:
  source_const_checked_builtin builtin args keywords = SC_Value v ==>
  source_const_value_ok v
Proof
  rw[source_const_checked_builtin_def, source_const_then_def, AllCaseEqs()] >> gvs[]
QED

Theorem source_const_builtin_arity_domain:
  source_const_builtin_arity builtin = SOME n /\ LENGTH args <> n ==>
  source_const_builtin builtin args keywords = SC_Invalid SCErr_Arity
Proof
  simp[source_const_builtin_def]
QED

Theorem source_const_builtin_keyword_domain:
  source_const_builtin_arity builtin = SOME n /\ LENGTH args = n /\
  keywords <> [] /\ (builtin <> SCB_MethodId \/ MAP FST keywords <> ["output_type"]) ==>
  source_const_builtin builtin args keywords = SC_Invalid SCErr_Keyword
Proof
  rw[source_const_builtin_def] >> gvs[]
QED

Theorem source_const_min_integer_domain:
  source_const_builtin SCB_Min [SCV_Int a; SCV_Int b] [] = SC_Value v <=>
  source_const_common_integer a b /\ v = SCV_Int (if a <= b then a else b)
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def,
       source_const_builtin_apply_def, source_const_builtin_numeric_def,
       AllCaseEqs(), EQ_SYM_EQ]
QED

Theorem source_const_abs_domain:
  source_const_builtin SCB_Abs [SCV_Int a] [] = SC_Value v <=>
  source_const_int256 a /\ source_const_int256 (ABS a) /\ v = SCV_Int (ABS a)
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def,
       source_const_builtin_apply_def, source_const_builtin_numeric_def,
       AllCaseEqs(), EQ_SYM_EQ, CONJ_ASSOC]
QED

Theorem source_const_modular_zero:
  source_const_builtin SCB_Uint256AddMod [SCV_Int a; SCV_Int b; SCV_Int 0] [] =
    SC_Invalid SCErr_ZeroDivisor /\
  source_const_builtin SCB_Uint256MulMod [SCV_Int a; SCV_Int b; SCV_Int 0] [] =
    SC_Invalid SCErr_ZeroDivisor
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def,
       source_const_builtin_apply_def, source_const_builtin_numeric_def]
QED

Theorem source_const_modular_operand_domains:
  source_const_builtin SCB_Uint256AddMod [SCV_Int a; SCV_Int b; SCV_Int c] [] = SC_Value v ==>
  source_const_uint256 a /\ source_const_uint256 b /\ source_const_uint256 c /\ c <> 0 /\
  v = SCV_Int ((a + b) % c)
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def,
       source_const_builtin_apply_def, source_const_builtin_numeric_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem source_const_power_double:
  (a:num) ** (2 * k) = a ** k * a ** k
Proof
  `2 * k = k + k` by decide_tac >> pop_assum SUBST1_TAC >> simp[EXP_ADD]
QED

Theorem source_const_modexp_correct:
  !n a. source_const_modexp a n = a ** n MOD (2 ** 256)
Proof
  completeInduct_on `n` >> rpt gen_tac >>
  Cases_on `n = 0` >- (gvs[] >> simp[Once source_const_modexp_def]) >>
  `n DIV 2 < n` by simp[] >>
  first_x_assum (qspec_then `n DIV 2` mp_tac) >> simp[] >> strip_tac >>
  simp[Once source_const_modexp_def] >>
  `n = n DIV 2 * 2 + n MOD 2` by
    (qspec_then `2` mp_tac arithmeticTheory.DIVISION >> simp[] >>
     disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  Cases_on `EVEN n` >> fs[EVEN_MOD2] >>
  `n MOD 2 = 0 \/ n MOD 2 = 1` by
    (`n MOD 2 < 2` by (irule arithmeticTheory.MOD_LESS >> simp[]) >> decide_tac) >>
  gvs[] >>
  qpat_x_assum `n = _` (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp_tac std_ss [EXP_ADD, EXP_2, source_const_power_double, EXP_1,
                   MULT_CLAUSES, AC MULT_ASSOC MULT_COMM]
QED

Theorem source_const_powmod256_domain:
  source_const_builtin SCB_PowMod256 [SCV_Int a; SCV_Int b] [] = SC_Value v <=>
  source_const_uint256 a /\ source_const_uint256 b /\
  v = SCV_Int (&(Num a ** Num b MOD (2 ** 256)))
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def,
       source_const_builtin_apply_def, source_const_builtin_numeric_def,
       source_const_modexp_correct, AllCaseEqs(), EQ_SYM_EQ, CONJ_ASSOC]
QED

Theorem source_const_len_fixed_bytes_invalid:
  source_const_builtin SCB_Len [SCV_Hex s] [] = SC_Invalid SCErr_Domain
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def,
       source_const_builtin_apply_def]
QED

Theorem source_const_keccak_specification:
  source_const_keccak bs = MAP w2n (Keccak_256_bytes (MAP (n2w:num -> word8) bs))
Proof
  simp[source_const_keccak_def, keccakTheory.Keccak_256_w64_thm]
QED

Theorem source_const_method_output_types:
  source_const_builtin SCB_MethodId [SCV_String s] [("output_type",SCV_BytesType fixed 4)] =
  source_const_method_id (SCV_String s) fixed
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def, source_const_builtin_apply_def]
QED

Theorem source_const_method_selector_order:
  EVERY (\c. ORD c < 128) s /\ ~MEM #" " s ==>
  source_const_builtin SCB_MethodId [SCV_String s] [] =
    SC_Value (SCV_Bytes (TAKE 4 (source_const_keccak (MAP ORD s)))) /\
  source_const_builtin SCB_MethodId [SCV_String s] [("output_type",SCV_BytesType T 4)] =
    SC_Value (SCV_Hex (source_const_hex_encode (TAKE 4 (source_const_keccak (MAP ORD s)))))
Proof
  simp[source_const_builtin_def, source_const_builtin_arity_def,
       source_const_builtin_apply_def, source_const_method_id_def]
QED

Theorem source_const_method_dynamic_invalid:
  source_const_eval env (SCE_Builtin SCB_MethodId [SCE_Dynamic] []) = SC_Invalid SCErr_Domain
Proof
  simp[source_const_eval_def, source_const_builtin_result_def, source_const_collect_def,
       source_const_combine_def]
QED
