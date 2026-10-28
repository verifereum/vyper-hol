Theory sourceConstEvalProps
Ancestors
  sourceConstEval sourceConstBuiltinProps integer
Libs
  intLib

(* ===== Collection boundaries ===== *)

Theorem source_const_collect_values:
  !rs vs. source_const_collect rs = SC_Value vs <=> rs = MAP SC_Value vs
Proof
  Induct >> rpt gen_tac >> Cases_on `vs` >> simp[source_const_collect_def] >>
  Cases_on `h` >> Cases_on `source_const_collect rs` >>
  gvs[source_const_combine_def]
QED

Theorem source_const_collect_invalid:
  !rs. (?e. source_const_collect rs = SC_Invalid e) <=>
       EXISTS (\r. ?e. r = SC_Invalid e) rs
Proof
  Induct >> rpt gen_tac >> simp[source_const_collect_def] >>
  Cases_on `h` >> Cases_on `source_const_collect rs` >>
  gvs[source_const_combine_def]
QED

Theorem source_const_combine_invalid_right:
  ?e. source_const_combine f left (SC_Invalid err) = SC_Invalid e
Proof
  Cases_on `left` >> simp[source_const_combine_def]
QED

Theorem source_const_unimplemented_not_value[simp]:
  source_const_unimplemented reason results <> SC_Value v
Proof
  Cases_on `source_const_collect results` >>
  simp[source_const_unimplemented_def]
QED

Theorem source_const_collect_no_dynamic_success:
  MEM SC_NotConstant rs ==> source_const_collect rs <> SC_Value vs
Proof
  rw[source_const_collect_values] >> strip_tac >>
  gvs[listTheory.MEM_MAP]
QED

Theorem source_const_then_success:
  source_const_then result f = SC_Value v <=>
  ?x. result = SC_Value x /\ f x = SC_Value v
Proof
  Cases_on `result` >> simp[source_const_then_def]
QED

Theorem source_const_combine_success:
  source_const_combine f left right = SC_Value v <=>
  ?l r. left = SC_Value l /\ right = SC_Value r /\ f l r = SC_Value v
Proof
  Cases_on `left` >> Cases_on `right` >> simp[source_const_combine_def]
QED

Theorem source_const_collect_value_ok:
  source_const_collect rs = SC_Value vs /\
  (!v. MEM (SC_Value v) rs ==> source_const_value_ok v) ==>
  EVERY source_const_value_ok vs
Proof
  simp[source_const_collect_values] >> strip_tac >>
  gvs[listTheory.MEM_MAP, listTheory.EVERY_MEM]
QED

Theorem source_const_collect_map_value_ok:
  source_const_collect (MAP f es) = SC_Value vs ==>
  (!e v. MEM e es /\ f e = SC_Value v ==> source_const_value_ok v) ==>
  EVERY source_const_value_ok vs
Proof
  rpt strip_tac >> irule source_const_collect_value_ok >>
  qexists_tac `MAP f es` >> simp[] >>
  rw[listTheory.MEM_MAP] >> metis_tac[]
QED

(* ===== Accepted domains and result invariants ===== *)

Theorem source_const_literal_value_ok:
  source_const_literal lit = SC_Value v ==> source_const_value_ok v
Proof
  Cases_on `lit` >>
  simp[source_const_literal_def, AllCaseEqs(), source_const_value_ok_def] >>
  rpt strip_tac >> gvs[source_const_value_ok_def]
QED

Theorem source_const_lookup_value_ok:
  source_const_lookup env path = SC_Value v ==> source_const_value_ok v
Proof
  rw[source_const_lookup_def, AllCaseEqs()] >>
  gvs[source_const_value_ok_def]
QED

Theorem source_const_unary_value_ok:
  source_const_unary uop arg = SC_Value v ==> source_const_value_ok v
Proof
  Cases_on `uop` >> Cases_on `arg` >>
  simp[source_const_unary_def, source_const_value_ok_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[source_const_value_ok_def]
QED

Theorem source_const_binary_value_ok:
  source_const_binary bop left right = SC_Value v ==> source_const_value_ok v
Proof
  Cases_on `left` >> Cases_on `right` >>
  simp[source_const_binary_def] >> Cases_on `bop` >>
  simp[source_const_integer_binary_def, source_const_power_def,
       source_const_decimal_binary_def, source_const_decimal_quantize_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[source_const_value_ok_def]
QED

Theorem source_const_compare_boolean:
  source_const_compare cop left right = SC_Value v ==> ?b. v = SCV_Bool b
Proof
  Cases_on `left` >> Cases_on `right` >> Cases_on `cop` >>
  simp[source_const_compare_def, source_const_integer_compare_def,
       source_const_membership_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem source_const_boolean_domain:
  source_const_boolean bop vs = SC_Value v ==>
  2 <= LENGTH vs /\ EVERY source_const_is_bool vs /\ ?b. v = SCV_Bool b
Proof
  Cases_on `bop` >> rw[source_const_boolean_def, AllCaseEqs()] >>
  gvs[listTheory.EVERY_MEM, combinTheory.o_DEF]
QED

Theorem source_const_not_domain:
  source_const_unary SCU_Not arg = SC_Value v <=>
  ?b. arg = SCV_Bool b /\ v = SCV_Bool (~b)
Proof
  Cases_on `arg` >> simp[source_const_unary_def, EQ_SYM_EQ]
QED

Theorem source_const_neg_integer:
  source_const_unary SCU_Neg (SCV_Int i) = SC_Value (SCV_Int (-i))
Proof
  simp[source_const_unary_def]
QED

Theorem source_const_ordered_bool_invalid:
  (cop = SCC_Lt \/ cop = SCC_Le \/ cop = SCC_Gt \/ cop = SCC_Ge) ==>
  source_const_compare cop (SCV_Bool a) (SCV_Bool b) = SC_Invalid SCErr_Domain
Proof
  rw[] >> simp[source_const_compare_def, source_const_equality_domain_def]
QED

Theorem source_const_integer_bool_distinct:
  source_const_binary bop (SCV_Int i) (SCV_Bool b) = SC_Invalid SCErr_Domain /\
  source_const_compare SCC_Eq (SCV_Int i) (SCV_Bool b) = SC_Invalid SCErr_Domain
Proof
  simp[source_const_binary_def, source_const_compare_def,
       source_const_equality_domain_def]
QED

Theorem source_const_divisor_domain:
  source_const_integer_binary SCB_FloorDiv a b = SC_Invalid SCErr_ZeroDivisor
    <=> b = 0
Proof
  simp[source_const_integer_binary_def] >> rw[]
QED

Theorem source_const_shift_domain:
  (?v. source_const_integer_binary SCB_LShift a b = SC_Value v) <=>
  0 <= b /\ b <= 256
Proof
  simp[source_const_integer_binary_def] >> rw[]
QED

Theorem source_const_quot_rem_standard:
  b <> 0 ==>
  source_const_quot a b = a quot b /\ source_const_rem a b = a rem b
Proof
  simp[source_const_quot_def, source_const_rem_def, int_rem]
QED

Theorem source_const_remainder_bounds:
  b <> 0 ==>
  ABS (source_const_rem a b) < ABS b /\
  (if 0 < a then 0 <= source_const_rem a b else source_const_rem a b <= 0)
Proof
  strip_tac >> drule INT_REMQUOT >>
  disch_then (qspec_then `a` strip_assume_tac) >>
  gvs[source_const_quot_rem_standard]
QED

Theorem source_const_div_rem_identity:
  a = source_const_quot a b * b + source_const_rem a b
Proof
  simp[source_const_rem_def]
QED

(* No source integer bound appears in this acceptance equation. Target-type
   representability and legality of the ORIGINAL typed expression are separate
   obligations for elaboration, not consequences of successful arithmetic. *)
Theorem source_const_add_unbounded:
  source_const_eval env
    (SCE_Binary SCB_Add (SCE_Literal (SCL_Int a)) (SCE_Literal (SCL_Int b))) =
  SC_Value (SCV_Int (a + b))
Proof
  simp[source_const_eval_def, source_const_literal_def,
       source_const_combine_def, source_const_binary_def,
       source_const_integer_binary_def]
QED

Theorem source_const_subscript_value_ok:
  source_const_value_ok left /\
  source_const_subscript left index = SC_Value v ==> source_const_value_ok v
Proof
  Cases_on `left` >> Cases_on `index` >>
  simp[source_const_subscript_def, source_const_value_ok_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rename1 `source_const_value_ok (EL (Num i) items)` >>
  fs[listTheory.EVERY_EL] >> first_x_assum irule >>
  Cases_on `i` >> gvs[] >> Cases_on `items` >> gvs[]
QED

Theorem source_const_eval_value_ok:
  !env expr. !v. source_const_eval env expr = SC_Value v ==>
                source_const_value_ok v
Proof
  ho_match_mp_tac source_const_eval_ind >> rpt conj_tac >>
  rpt gen_tac >>
  simp[Once source_const_eval_def, source_const_then_success,
       source_const_combine_success, source_const_builtin_result_success] >>
  rpt strip_tac >> gvs[] >>
  FIRST [drule source_const_checked_builtin_value_ok >> simp[],
         drule source_const_bytes_type_value_ok >> simp[],
         drule source_const_literal_value_ok >> simp[],
         drule source_const_lookup_value_ok >> simp[],
         drule source_const_unary_value_ok >> simp[],
         drule source_const_binary_value_ok >> simp[],
         drule_all source_const_subscript_value_ok >> simp[],
         drule source_const_compare_boolean >> rw[] >>
           simp[source_const_value_ok_def],
         drule source_const_boolean_domain >> rw[] >>
           simp[source_const_value_ok_def],
         gvs[source_const_tuple_def, AllCaseEqs(), source_const_value_ok_def] >>
           drule source_const_collect_map_value_ok >> impl_tac
           >- (rw[] >> res_tac) >> simp[listTheory.EVERY_MEM]]
QED

(* ===== Eager errors, including dynamic/unsupported contexts ===== *)

Theorem source_const_boolean_invalid_child:
  MEM (SC_Invalid err) (MAP (source_const_eval env) es) ==>
  ?e. source_const_eval env (SCE_Boolean bop es) = SC_Invalid e
Proof
  strip_tac >>
  `?e. source_const_collect (MAP (source_const_eval env) es) = SC_Invalid e` by
    (simp[source_const_collect_invalid, listTheory.EXISTS_MEM] >>
     metis_tac[]) >>
  ONCE_REWRITE_TAC[source_const_eval_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[source_const_then_def]
QED

Theorem source_const_dynamic_zero_division:
  source_const_eval env
    (SCE_Binary SCB_Add SCE_Dynamic
      (SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1))
                              (SCE_Literal (SCL_Int 0)))) =
  SC_Invalid SCErr_ZeroDivisor
Proof
  simp[source_const_eval_def, source_const_combine_def,
       source_const_literal_def, source_const_binary_def,
       source_const_integer_binary_def]
QED

Theorem source_const_false_and_zero_division:
  source_const_eval env
    (SCE_Boolean SCB_And
      [SCE_Literal (SCL_Bool F);
       SCE_Compare SCC_Eq
         (SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1))
                                 (SCE_Literal (SCL_Int 0)))
         (SCE_Literal (SCL_Int 0))]) = SC_Invalid SCErr_ZeroDivisor
Proof
  simp[source_const_eval_def, source_const_collect_def,
       source_const_combine_def, source_const_then_def,
       source_const_literal_def, source_const_binary_def,
       source_const_integer_binary_def]
QED

Theorem source_const_unsupported_zero_division:
  source_const_eval env
    (SCE_Unsupported "future"
      [SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1))
                              (SCE_Literal (SCL_Int 0))]) =
  SC_Invalid SCErr_ZeroDivisor
Proof
  simp[source_const_eval_def, source_const_unimplemented_def, source_const_collect_def,
       source_const_combine_def, source_const_then_def,
       source_const_literal_def, source_const_binary_def,
       source_const_integer_binary_def]
QED

(* ===== Executable source-semantic regression probes ===== *)

Theorem source_const_signed_division_examples:
  source_const_quot (-7) 3 = -2 /\ source_const_rem (-7) 3 = -1 /\
  source_const_quot 7 (-3) = -2 /\ source_const_rem 7 (-3) = 1 /\
  source_const_quot (-7) (-3) = 2 /\ source_const_rem (-7) (-3) = -1
Proof
  EVAL_TAC
QED

Theorem source_const_unwrapped_shift_bound_example:
  source_const_eval []
    (SCE_Binary SCB_Add
      (SCE_Binary SCB_RShift
        (SCE_Binary SCB_LShift (SCE_Literal (SCL_Int 1))
                              (SCE_Literal (SCL_Int 256)))
        (SCE_Literal (SCL_Int 255)))
      (SCE_Literal (SCL_Int 1))) = SC_Value (SCV_Int 3)
Proof
  EVAL_TAC
QED

Theorem source_const_shift_rejection_examples:
  source_const_integer_binary SCB_LShift 1 257 = SC_Invalid SCErr_ShiftCount /\
  source_const_integer_binary SCB_RShift 1 (-1) = SC_Invalid SCErr_ShiftCount /\
  source_const_integer_binary SCB_RShift (-3) 1 = SC_Value (SCV_Int (-2))
Proof
  EVAL_TAC
QED

Theorem source_const_literal_examples:
  source_const_literal (SCL_Decimal (-123) 2) =
    SC_Value (SCV_Decimal (-12300000000)) /\
  source_const_literal (SCL_Decimal 1 11) = SC_Invalid SCErr_DecimalPrecision /\
  source_const_literal (SCL_Bytes [0;255]) = SC_Value (SCV_Bytes [0;255]) /\
  source_const_literal (SCL_Bytes [256]) = SC_Invalid SCErr_Octet /\
  source_const_literal (SCL_String "hello") = SC_Value (SCV_String "hello")
Proof
  EVAL_TAC
QED

Theorem source_const_aggregate_example:
  source_const_eval []
    (SCE_Tuple [SCE_List [SCE_Literal (SCL_Int 4)];
                SCE_Literal (SCL_Bool T)]) =
  SC_Value (SCV_Tuple [SCV_List [SCV_Int 4]; SCV_Bool T])
Proof
  EVAL_TAC
QED

Theorem source_const_boolean_examples:
  source_const_eval [] (SCE_Boolean SCB_And
    [SCE_Literal (SCL_Bool T); SCE_Literal (SCL_Bool F)]) =
      SC_Value (SCV_Bool F) /\
  source_const_eval [] (SCE_Boolean SCB_Or
    [SCE_Literal (SCL_Bool F); SCE_Literal (SCL_Bool T)]) =
      SC_Value (SCV_Bool T) /\
  source_const_boolean SCB_And [] = SC_Invalid SCErr_BooleanArity /\
  source_const_boolean SCB_And [SCV_Bool F; SCV_Int 0] = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_literal_kind_examples:
  source_const_compare SCC_Eq (SCV_String "a") (SCV_String "a") =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_NotEq (SCV_Hex "0xaB") (SCV_Hex "0xac") =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_Eq (SCV_Hex "0xaB") (SCV_Bytes [171]) =
    SC_Invalid SCErr_Domain /\
  source_const_compare SCC_Lt (SCV_String "a") (SCV_String "b") =
    SC_Invalid SCErr_Domain /\
  source_const_literal (SCL_String [CHR 128]) = SC_Invalid SCErr_StringCharacter
Proof
  EVAL_TAC
QED

Theorem source_const_unary_and_unsupported_examples:
  source_const_unary SCU_Invert (SCV_Int 0) =
    SC_Value (SCV_Int (2 ** 256 - 1)) /\
  source_const_unary SCU_Not (SCV_Int 0) = SC_Invalid SCErr_Domain /\
  source_const_unary SCU_Neg (SCV_Bool T) = SC_Invalid SCErr_Domain /\
  source_const_integer_binary SCB_Mod 7 0 = SC_Invalid SCErr_ZeroDivisor /\
  source_const_integer_binary SCB_Div 7 2 = SC_Invalid SCErr_Domain /\
  source_const_integer_binary SCB_Pow 2 3 = SC_Value (SCV_Int 8) /\
  source_const_binary SCB_Mul (SCV_Decimal 1) (SCV_Decimal 2) =
    SC_Value (SCV_Decimal 0)
Proof
  EVAL_TAC
QED

Theorem source_const_builtin_keyword_eager:
  source_const_eval [] (SCE_Builtin SCB_MethodId [SCE_Dynamic]
    [("output_type", SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1))
                                          (SCE_Literal (SCL_Int 0)))]) =
    SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem source_const_name_examples:
  source_const_eval [] (SCE_Name ["missing"]) =
    SC_Unsupported (SCS_UnresolvedName ["missing"]) /\
  source_const_eval [(["local"],SC_DynamicBinding)] (SCE_Name ["local"]) =
    SC_NotConstant /\
  source_const_eval [(["C"],SC_Constant (SCV_Bytes [256]))] (SCE_Name ["C"]) =
    SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_unimplemented_dynamic:
  source_const_eval [] (SCE_Builtin SCB_MethodId [SCE_Dynamic] []) =
    SC_Invalid SCErr_Domain /\
  source_const_eval [] (SCE_Unsupported "future" [SCE_Dynamic]) =
    SC_Unsupported (SCS_Syntax "future")
Proof
  EVAL_TAC
QED

Theorem source_const_builtin_not_spelling:
  source_const_eval [] (SCE_Call (SCE_Literal (SCL_String "method_id"))
    [SCE_Literal (SCL_String "foo()")] []) = SC_Unsupported SCS_Call /\
  source_const_eval [] (SCE_Call (SCE_Name ["method_id"])
    [SCE_Literal (SCL_String "foo()")] []) =
  SC_Unsupported (SCS_UnresolvedName ["method_id"])
Proof
  EVAL_TAC
QED

(* ===== Decimal, power, membership and literal-list boundaries ===== *)

Theorem source_const_decimal_comparison:
  cop <> SCC_In /\ cop <> SCC_NotIn ==>
  source_const_compare cop (SCV_Decimal a) (SCV_Decimal b) =
  source_const_integer_compare cop a b
Proof
  simp[source_const_compare_def]
QED

Theorem source_const_power_negative_domain:
  source_const_power a b = SC_Invalid SCErr_NegativePower <=> b < 0
Proof
  simp[source_const_power_def, AllCaseEqs()] >> rw[]
QED

Theorem source_const_power_computation:
  0 < b /\ 1 < ABS a /\ b < 258 /\ ABS a < 2 ** 258 /\
  (ABS (a ** Num b) <= 2 ** 256 \/ ABS (a ** Num b) = 2 ** 257) ==>
  source_const_power a b = SC_Value (SCV_Int (a ** Num b))
Proof
  rpt strip_tac >>
  `~(b < 0) /\ b <> 0 /\ ~(ABS a <= 1) /\
   ~(258 <= b) /\ ~(2 ** 258 <= ABS a)` by intLib.ARITH_TAC >>
  simp[source_const_power_def]
QED

Theorem source_const_decimal_mul_quantizes:
  source_const_decimal_small a /\ source_const_decimal_small b ==>
  source_const_binary SCB_Mul (SCV_Decimal a) (SCV_Decimal b) =
  source_const_decimal_quantize
    (source_const_quot (source_const_context (a * b)) (10 ** 10))
Proof
  simp[source_const_binary_def, source_const_decimal_binary_def]
QED

Theorem source_const_decimal_context_boundary:
  ~source_const_decimal_small a ==>
  source_const_decimal_binary SCB_Add a b = SC_Unsupported SCS_DecimalOperation
Proof
  simp[source_const_decimal_binary_def]
QED

Theorem source_const_decimal_zero_divisors:
  source_const_decimal_binary SCB_Div a 0 = SC_Invalid SCErr_ZeroDivisor /\
  source_const_decimal_binary SCB_FloorDiv a 0 = SC_Invalid SCErr_ZeroDivisor /\
  source_const_decimal_binary SCB_Mod a 0 = SC_Invalid SCErr_ZeroDivisor
Proof
  simp[source_const_decimal_binary_def]
QED

Theorem source_const_membership_domain:
  source_const_membership cop left (SCV_List vs) = SC_Value v ==>
  source_const_kind left < 6 /\ EVERY (\x. source_const_kind x < 6) vs /\
  source_const_homogeneous vs /\ ?b. v = SCV_Bool b
Proof
  simp[source_const_membership_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem source_const_subscript_success:
  source_const_subscript (SCV_List vs) (SCV_Int i) = SC_Value v <=>
  source_const_homogeneous vs /\
  ~EXISTS (\x. source_const_kind x = 8) vs /\
  0 <= i /\ i < &(LENGTH vs) /\ v = EL (Num i) vs
Proof
  simp[source_const_subscript_def, AllCaseEqs(), EQ_SYM_EQ,
       INT_NOT_LT, INT_NOT_LE, CONJ_ASSOC]
QED

Theorem source_const_decimal_arithmetic_examples:
  source_const_decimal_binary SCB_Add 12300000000 23400000000 =
    SC_Value (SCV_Decimal 35700000000) /\
  source_const_decimal_binary SCB_Sub 12300000000 23400000000 =
    SC_Value (SCV_Decimal (-11100000000)) /\
  source_const_decimal_binary SCB_Mul 3333333333 3333333333 =
    SC_Value (SCV_Decimal 1111111110) /\
  source_const_decimal_binary SCB_Mul (-3333333333) 3333333333 =
    SC_Value (SCV_Decimal (-1111111110)) /\
  source_const_decimal_binary SCB_Div (-10000000000) 30000000000 =
    SC_Value (SCV_Decimal (-3333333333)) /\
  source_const_decimal_binary SCB_Mod (-75000000000) 20000000000 =
    SC_Value (SCV_Decimal (-15000000000))
Proof
  EVAL_TAC
QED

(* Truncate at EACH operation: do not keep an exact rational until the root. *)
Theorem source_const_decimal_per_operation:
  source_const_eval []
    (SCE_Binary SCB_Mul
      (SCE_Binary SCB_Div (SCE_Literal (SCL_Decimal 1 0))
                          (SCE_Literal (SCL_Decimal 3 0)))
      (SCE_Literal (SCL_Decimal 3 0))) =
    SC_Value (SCV_Decimal 9999999999)
Proof
  EVAL_TAC
QED

Theorem source_const_decimal_domain_examples:
  source_const_decimal_binary SCB_Pow 10000000000 20000000000 =
    SC_Invalid SCErr_Domain /\
  source_const_decimal_binary SCB_FloorDiv 10000000000 20000000000 =
    SC_Invalid SCErr_Domain /\
  source_const_decimal_binary SCB_BitAnd 1 2 = SC_Invalid SCErr_Domain /\
  source_const_decimal_binary SCB_LShift 1 (-1) = SC_Invalid SCErr_ShiftCount /\
  source_const_decimal_binary SCB_RShift 1 10000000000 = SC_Invalid SCErr_Domain /\
  source_const_binary SCB_Add (SCV_Decimal 1) (SCV_Int 1) =
    SC_Invalid SCErr_Domain /\
  source_const_compare SCC_Lt (SCV_Decimal (-1)) (SCV_Decimal 0) =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_Eq (SCV_Decimal 10000000000) (SCV_Int 1) =
    SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_decimal_context_examples:
  source_const_context (10 ** 78 + 15) = 10 ** 78 + 20 /\
  source_const_context (10 ** 78 + 5) = 10 ** 78 /\
  source_const_decimal_binary SCB_Mul (10 ** 49) (10 ** 49) =
    SC_Invalid SCErr_DecimalPrecision /\
  source_const_decimal_binary SCB_Mod (10 ** 78) 1 =
    SC_Invalid SCErr_DecimalPrecision /\
  source_const_decimal_binary SCB_Add (10 ** 78) 0 =
    SC_Value (SCV_Decimal (10 ** 78))
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem source_const_decimal_context_before_quantize:
  source_const_decimal_binary SCB_Mul (10 ** 44 - 1) (10 ** 44 + 1) =
    SC_Invalid SCErr_DecimalPrecision /\
  source_const_decimal_binary SCB_Div (10 ** 79 - 1) (10 ** 79) =
    SC_Value (SCV_Decimal (10 ** 10)) /\
  source_const_decimal_binary SCB_Div (10 ** 78 + 6) (10 ** 11 + 1) =
    SC_Value (SCV_Decimal (source_const_quot (10 ** 88) (10 ** 11 + 1))) /\
  source_const_decimal_binary SCB_Div (-(10 ** 78 + 6)) (10 ** 11 + 1) =
    SC_Value (SCV_Decimal (-(source_const_quot (10 ** 88) (10 ** 11 + 1) + 1)))
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >> EVAL_TAC
QED

Theorem source_const_power_examples:
  source_const_power 0 0 = SC_Value (SCV_Int 1) /\
  source_const_power 0 1000000000000000000000 = SC_Value (SCV_Int 0) /\
  source_const_power (-1) 1000000000000000000001 = SC_Value (SCV_Int (-1)) /\
  source_const_power 1 1000000000000000000001 = SC_Value (SCV_Int 1) /\
  source_const_power (-2) 3 = SC_Value (SCV_Int (-8)) /\
  source_const_power 2 (-1) = SC_Invalid SCErr_NegativePower /\
  source_const_power 2 256 = SC_Value (SCV_Int (2 ** 256)) /\
  source_const_power 2 257 = SC_Value (SCV_Int (2 ** 257)) /\
  source_const_power (-2) 258 = SC_Invalid SCErr_PowerBound /\
  source_const_power (2 ** 256 + 1) 1 = SC_Unsupported SCS_Power
Proof
  EVAL_TAC
QED

Theorem source_const_membership_examples:
  source_const_compare SCC_In (SCV_Bool T) (SCV_List [SCV_Int 1]) =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_In (SCV_Int 1) (SCV_List [SCV_Decimal 10000000000]) =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_In (SCV_Hex "0xAB") (SCV_List [SCV_Hex "0xab"]) =
    SC_Value (SCV_Bool F) /\
  source_const_compare SCC_Eq (SCV_Hex "0xAB") (SCV_Hex "0xab") =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_In (SCV_String "0xAB") (SCV_List [SCV_Hex "0xAB"]) =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_NotIn (SCV_Int 0) (SCV_List []) =
    SC_Value (SCV_Bool T) /\
  source_const_compare SCC_In (SCV_Int 1) (SCV_List [SCV_Int 1; SCV_Bool T]) =
    SC_Invalid SCErr_Domain /\
  source_const_compare SCC_In (SCV_Int 1) (SCV_Tuple [SCV_Int 1]) =
    SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_subscript_examples:
  source_const_eval [] (SCE_Subscript
    (SCE_List [SCE_List [SCE_Literal (SCL_Int 1)];
               SCE_List [SCE_Literal (SCL_Bool T)]]) (SCE_Literal (SCL_Int 1))) =
    SC_Value (SCV_List [SCV_Bool T]) /\
  source_const_subscript (SCV_List [SCV_Int 1; SCV_Bool T]) (SCV_Int 0) =
    SC_Invalid SCErr_Domain /\
  source_const_subscript (SCV_List [SCV_Int 1]) (SCV_Int (-1)) =
    SC_Invalid SCErr_Index /\
  source_const_subscript (SCV_List [SCV_Int 1]) (SCV_Int 1) =
    SC_Invalid SCErr_Index /\
  source_const_subscript (SCV_List []) (SCV_Int 0) = SC_Invalid SCErr_Index /\
  source_const_subscript (SCV_List [SCV_Int 1]) (SCV_Bool F) =
    SC_Invalid SCErr_Domain /\
  source_const_subscript (SCV_Tuple [SCV_Int 1]) (SCV_Int 0) =
    SC_Invalid SCErr_Domain /\
  source_const_subscript (SCV_Bytes [1]) (SCV_Int 0) = SC_Invalid SCErr_Domain
Proof
  EVAL_TAC
QED

Theorem source_const_hex_token_examples:
  source_const_literal (SCL_Hex "0xaB") = SC_Value (SCV_Hex "0xaB") /\
  source_const_literal (SCL_Hex "0Xab") = SC_Invalid SCErr_HexToken /\
  source_const_literal (SCL_Hex "0x0") = SC_Invalid SCErr_HexToken /\
  source_const_literal (SCL_Hex "0xgg") = SC_Invalid SCErr_HexToken
Proof
  EVAL_TAC
QED

Theorem source_const_unselected_element_eager:
  source_const_eval [] (SCE_Subscript
    (SCE_List [SCE_Literal (SCL_Int 1);
               SCE_Binary SCB_FloorDiv (SCE_Literal (SCL_Int 1))
                                      (SCE_Literal (SCL_Int 0))])
    (SCE_Literal (SCL_Int 0))) = SC_Invalid SCErr_ZeroDivisor
Proof
  EVAL_TAC
QED

Theorem source_const_new_forms_eager:
  source_const_eval [] (SCE_Subscript SCE_Dynamic
    (SCE_Binary SCB_Div (SCE_Literal (SCL_Decimal 1 0))
                         (SCE_Literal (SCL_Decimal 0 0)))) =
    SC_Invalid SCErr_ZeroDivisor /\
  source_const_eval [] (SCE_Compare SCC_In (SCE_Literal (SCL_Int 0))
    (SCE_List [SCE_Dynamic; SCE_Binary SCB_Pow (SCE_Literal (SCL_Int 2))
                                              (SCE_Literal (SCL_Int (-1)))])) =
    SC_Invalid SCErr_NegativePower
Proof
  EVAL_TAC
QED

(* ===== Kernel closure audit of every exported object ===== *)

fun audit_source_const_theory thy =
  let
    val exports = DB.thms thy
    fun check (name, th) =
      let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
      in
        if null (Thm.hyp th) andalso null axioms andalso
           List.all (fn s => s = "DISK_THM") oracles then ()
        else raise Fail ("source constant kernel audit failed: " ^ thy ^ "." ^ name)
      end
  in
    List.app check exports;
    print ("SOURCE_CONST_KERNEL_CLOSED " ^ thy ^ " exports=" ^
           Int.toString (length exports) ^ "\n")
  end;

val () = List.app audit_source_const_theory
  ["sourceConstAST", "sourceConstBuiltin", "sourceConstEval",
   "sourceConstBuiltinProps", "sourceConstEvalProps"];
