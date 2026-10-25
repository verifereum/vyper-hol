(*
 * Expression simulation: the operators (#636, Operators)
 *
 * The case lemmas of compile_expr_sim (exprSimMain) for the operators and
 * the conditional expression.
 *
 * TOP-LEVEL:
 *   compile_bop_case_sim     — a binary operator: on operands of
 *                              word_value_type by compile_bop_word_sim, the
 *                              rest by compile_bop_other_sim
 *   compile_bop_word_sim     — compile_bop_sim (exprSimOps) from the
 *                              operands' expr_sim_ok and binop_frag_typed
 *   expr_sim_pre_bop         — the operands of a well-typed binary operator
 *                              meet expr_sim_pre
 *   compile_not_sim, compile_neg_sim, compile_abs_sim — not, unary -, abs
 *   compile_ifexp_sim        — x if c else y: compile_ifexp_word_sim for
 *                              word types, compile_ifexp_aggregate_sim for
 *                              the rest
 *
 * Cheated, for the later #636 PRs:
 *   binop_frag_pow, binop_frag_shift_572, binop_frag_unsafe_width
 *                            — the cases of binop_frag_typed (the
 *                              operator's fragment on typed word operands)
 *                              that #692's lemmas don't cover: ** and
 *                              pow_mod (#572); shifts of integers narrower
 *                              than 256 bits, which well_typed_binop admits
 *                              but Vyper rejects and the lowering does not
 *                              truncate, and shifts by a negative amount
 *                              (#572); unsafe arithmetic on integer widths
 *                              that aren't whole bytes, which evaluate_type
 *                              admits but Vyper doesn't have.
 *                              binop_frag_typed dispatches every other
 *                              operator onto #692's lemmas.  Operators rows
 *                              2-5.
 *   compile_bop_other_sim    — == and != on address, bytesN and bytestrings
 *                              (msg.sender == owner lands here),
 *                              in and not in on arrays (#569), Operators
 *                              row 6
 *   compile_not_sim, compile_neg_sim (#572), compile_abs_sim — row 7
 *   compile_ifexp_aggregate_sim — row 9 for aggregate ternaries (#561,
 *                              #674); word ternaries are proved but for
 *                              lower_value_word_shape
 *                              (compile_ifexp_word_sim), and so are row 8's
 *                              and/or chains (#556), which the frontend
 *                              desugars to nested IfExps of type bool
 *                              (translate_boolop).  Bop And/Or are the
 *                              bitwise & and |.
 *
 * Compile-side facts, cheated (the shape #674's compile_expr_shape
 * proves for the shape judgment):
 *   lower_value_word_shape   — lowering a word-typed expression only
 *                              appends, hands out its variables, and
 *                              returns a variable it handed out or a literal
 *   compile_binop_shape      — compile_binop only appends
 * compile_bop_word_sim rests on these two and on binop_frag_typed, and
 * compile_ifexp_word_sim and exprSimConvert's compile_convert_word_sim on
 * lower_value_word_shape.  lower_value_word_shape and compile_binop_shape
 * are for word types only; the compound non-word cases need #674's
 * compile_expr_shape.
 *)

Theory exprSimOperators
Ancestors
  list finite_map
  fragExec exprSim exprSimHyps exprSimOps exprSimIfExp exprSimCompare
  exprSimArith exprBopLowering
  loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness

(* ===== Compile-side facts ===== *)

Theorem lower_value_word_shape:
  !cenv ty e sa op sb.
    lower_value compile_expr cenv ty e sa = (op, sb) /\
    is_word_type (expr_type e) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb.cs_next_id /\
    (!z. op = Var z ==> not_fresh_at sb z) /\ (!l. op <> Label l)
Proof
  cheat
QED

Theorem compile_binop_shape:
  !bop x y ty bl el sa op sb.
    compile_binop bop x y ty bl el sa = (op, sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  cheat
QED

(* ===== Binary operators ===== *)

Theorem word_value_type_word:
  !t. word_value_type t ==>
      is_word_type t /\ ~is_ArrayT t /\ ~is_bytestring_type t
Proof
  Cases >> simp[word_value_type_def, is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt`) >>
  simp[is_word_type_def, is_bytestring_type_def]
QED

Theorem well_typed_binop_word_result:
  !ann bop t1 t2.
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 ==>
    is_word_type ann
Proof
  rpt strip_tac >> drule word_value_type_word >> strip_tac >>
  Cases_on `bop` >> gvs[well_typed_binop_def, is_word_type_def]
QED

(* The type and the value of a typed operand of a word_value_type. *)
Theorem word_value_type_value_cases:
  !tenv t tv v.
    word_value_type t /\ evaluate_type tenv t = SOME tv /\
    value_has_type tv v ==>
    (?n i. t = BaseT (UintT n) /\ tv = BaseTV (UintT n) /\ v = IntV i /\
           0 < n /\ n <= 256 /\ within_int_bound (Unsigned n) i) \/
    (?n i. t = BaseT (IntT n) /\ tv = BaseTV (IntT n) /\ v = IntV i /\
           1 < n /\ n <= 256 /\ within_int_bound (Signed n) i) \/
    (?d. t = BaseT DecimalT /\ tv = BaseTV DecimalT /\ v = DecimalV d /\
         within_int_bound (Signed 168) d) \/
    (?b. t = BaseT BoolT /\ tv = BaseTV BoolT /\ v = BoolV b) \/
    (?nsid m k. t = FlagT nsid /\ tv = FlagTV m /\ v = FlagV k /\ m <= 256)
Proof
  rpt strip_tac >>
  `(?n. t = BaseT (UintT n)) \/ (?n. t = BaseT (IntT n)) \/
   t = BaseT DecimalT \/ t = BaseT BoolT \/ (?nsid. t = FlagT nsid)` by
    (Cases_on `t` >> fs[word_value_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_int_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, vyperValueTheory.within_int_bound_def]
QED

(* A typed value of an integer type. *)
Theorem int_type_value:
  !tenv ty tv v.
    is_int_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
    ?i. v = IntV i /\ 0 < type_bits ty /\ type_bits ty <= 256 /\
        type_to_int_bound ty =
          SOME (if is_signed_type ty then Signed (type_bits ty)
                else Unsigned (type_bits ty)) /\
        within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                          else Unsigned (type_bits ty)) i
Proof
  rpt strip_tac >>
  `word_value_type ty` by gvs[word_value_type_def] >>
  qspecl_then [`tenv`, `ty`, `tv`, `v`] mp_tac word_value_type_value_cases >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  gvs[type_to_int_bound_def, type_bits_def, is_signed_type_def]
QED

(* Checked + - * / % on two integers of one type. *)
Theorem binop_frag_int_arith:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ is_int_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  Cases_on `bop` >> fs[]
  >~ [`binop_frag _ _ _ _ Div`] >- (irule compile_divmod_sim >> simp[])
  >~ [`binop_frag _ _ _ _ Mod`] >- (irule compile_divmod_sim >> simp[]) >>
  irule compile_checked_sim >> simp[]
QED

(* A typed value of type decimal. *)
Theorem decimal_type_value:
  !tenv tv v.
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\ value_has_type tv v ==>
    ?d. v = DecimalV d /\ within_int_bound (Signed 168) d
Proof
  rw[vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]
QED

(* Checked + - * / % on two decimals. *)
Theorem binop_frag_decimal_arith:
  !ctx func cenv cx bop bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop (BaseT DecimalT) (BaseT DecimalT) bl el
      tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `tv`, `v1`] mp_tac decimal_type_value >>
  qspecl_then [`tenv`, `tv`, `v2`] mp_tac decimal_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  Cases_on `MEM bop [Mul; Div]`
  >- (irule compile_decimal_mul_div_sim >> simp[]) >>
  irule compile_decimal_add_sub_mod_sim >> simp[] >>
  Cases_on `bop` >> fs[]
QED

(* The wrapping operators on two integers of one type of a whole number of
   bytes. *)
Theorem binop_frag_unsafe_typed:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    is_int_type ty /\ type_bits ty MOD 8 = 0 /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule compile_unsafe_sim >> simp[]
QED

(* The comparisons, min and max on two word values of one type. *)
Theorem binop_frag_compare_typed:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0 tenv tv.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt strip_tac >>
  `word_value v1 /\ (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
   !m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256` by
    (qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac
       word_value_type_value_cases >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     gvs[word_value_def, is_uint256_def]) >>
  Cases_on `bop = Min \/ bop = Max`
  >- (irule compile_minmax_sim >> metis_tac[]) >>
  irule compile_compare_sim >> gvs[] >> metis_tac[]
QED

(* & | ^ on two word values of one type. *)
Theorem binop_frag_bitwise_typed:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    (bop = And \/ bop = Or \/ bop = XOr) /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> irule compile_bitwise_sim >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac word_value_type_value_cases >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac word_value_type_value_cases >>
  asm_rewrite_tac[] >> rpt strip_tac >> gvs[type_to_int_bound_def]
QED

(* Flag membership on two flags of one type. *)
Theorem binop_frag_flag_in_typed:
  !ctx func cenv cx bop nsid ty ann bl el tys v1 v2 es0 tenv tv.
    (bop = In \/ bop = NotIn) /\
    evaluate_type tenv (FlagT nsid) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  irule compile_flag_in_sim >> metis_tac[]
QED

(* A non-negative integer within the bound of an integer type of at most
   256 bits is a uint256. *)
Theorem within_int_bound_unsigned_256:
  !u n i.
    (u = Unsigned n \/ u = Signed n) /\ n <= 256 /\ within_int_bound u i /\
    0 <= i ==>
    within_int_bound (Unsigned 256) i
Proof
  rpt strip_tac >>
  `?k. i = &k` by metis_tac[integerTheory.NUM_POSINT_EXISTS] >>
  `k < 2 ** n` by
    (gvs[vyperValueTheory.within_int_bound_def] >> Cases_on `0 < n` >>
     gvs[] >> irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
     qexists_tac `2 ** (n - 1)` >> simp[arithmeticTheory.EXP_BASE_LE_MONO]) >>
  simp[vyperValueTheory.within_int_bound_def] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >> qexists_tac `2 ** n` >>
  simp[arithmeticTheory.EXP_BASE_LE_MONO]
QED

(* << and >> on a 256-bit integer by a non-negative amount. *)
Theorem binop_frag_shift_typed:
  !ctx func cenv cx bop ty t2 bl el tys v1 v2 es0 tenv tv1 tv2 i2.
    (bop = ShL \/ bop = ShR) /\ is_int_type ty /\ type_bits ty = 256 /\
    is_int_type t2 /\ v2 = IntV i2 /\ 0 <= i2 /\
    evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `within_int_bound (Unsigned 256) i2` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  irule compile_shift_sim >> gvs[]
QED

(* The cases #572 tracks, where the lowering does not compute the source's
   result, cheated until its lowering fix: ** (compile_safe_pow's EXP
   wraps where the source reverts unless an operand is a literal) and
   pow_mod (ExpMod falls through compile_binop to INVALID). *)
Theorem binop_frag_pow:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0.
    bop = Exp \/ bop = ExpMod ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* Shifts of an integer narrower than 256 bits, which the lowering does not
   truncate, or by a negative amount, where the source raises and the
   lowering shifts (#572).  Vyper rejects shifts of types other than int256
   and uint256; well_typed_binop admits every integer type. *)
Theorem binop_frag_shift_572:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0.
    (bop = ShL \/ bop = ShR) /\
    (type_bits ty < 256 \/ ?i. v2 = IntV i /\ i < 0) ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* The wrapping operators on an integer type whose width is not a whole
   number of bytes.  evaluate_type admits every width up to 256, but
   wrap_truncate sign-extends from a byte boundary, as Python does; Vyper
   has only integer types of whole bytes. *)
Theorem binop_frag_unsafe_width:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    type_bits ty MOD 8 <> 0 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* Each operator on typed operands of word_value_types, by its group. *)
Theorem binop_frag_arith_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_numeric_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  Cases_on `ann = BaseT DecimalT`
  >- (pop_assum SUBST_ALL_TAC >> irule binop_frag_decimal_arith >>
      metis_tac[]) >>
  irule binop_frag_int_arith >> gvs[] >> metis_tac[]
QED

Theorem binop_frag_unsafe_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `type_bits t1 MOD 8 = 0`
  >~ [`type_bits t1 MOD 8 <> 0`]
  >- (irule binop_frag_unsafe_width >> gvs[]) >>
  `t1 = ann /\ t2 = ann /\ is_int_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  irule binop_frag_unsafe_typed >> metis_tac[]
QED

Theorem binop_frag_shift_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `type_bits t1 < 256 \/ ?i. v2 = IntV i /\ i < 0`
  >- (irule binop_frag_shift_572 >> conj_tac >> first_assum ACCEPT_TAC) >>
  `t1 = ann /\ is_int_type ann /\ is_int_type t2` by
    gvs[well_typed_binop_def] >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  qpat_x_assum `v2 = IntV _` SUBST_ALL_TAC >>
  rename1 `value_has_type tv2 (IntV i2)` >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `t2`, `bl`, `el`,
               `tys`, `v1`, `IntV i2`, `es0`, `tenv`, `tv1`, `tv2`, `i2`]
    mp_tac binop_frag_shift_typed >>
  impl_tac >- gvs[integerTheory.INT_NOT_LT] >> simp[]
QED

Theorem binop_frag_in_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = In \/ bop = NotIn) /\ well_typed_binop ann bop t1 t2 /\
    word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `?nsid. t1 = FlagT nsid /\ t2 = FlagT nsid` by
    (Cases_on `t2` >> gvs[well_typed_binop_def, word_value_type_def]) >>
  gvs[] >> irule binop_frag_flag_in_typed >> metis_tac[]
QED

Theorem binop_frag_rest_any:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [And; Or; XOr; Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `t2 = t1` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t2 = t1` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (`ann = t1` by
        (qpat_x_assum `bop = _ \/ _` strip_assume_tac >>
         gvs[well_typed_binop_def]) >>
      pop_assum SUBST_ALL_TAC >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `t1`, `bl`, `el`, `tys`,
                   `v1`, `v2`, `es0`, `tenv`, `tv1`]
        mp_tac binop_frag_bitwise_typed >>
      impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `t1`, `ann`, `bl`, `el`,
               `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`]
    mp_tac binop_frag_compare_typed >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >> simp[]
QED

(* Instantiates a dispatch lemma above at the current goal's variables and
   discharges its premises from the assumptions. *)
fun binop_dispatch_tac th =
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `t1`, `t2`, `bl`,
               `el`, `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`, `tv2`]
    mp_tac th >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >>
  simp[];

Theorem binop_frag_word_typed:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    well_typed_binop ann bop t1 t2 /\
    word_value_type t1 /\ word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bop = Exp \/ bop = ExpMod`
  >- (irule binop_frag_pow >> first_assum ACCEPT_TAC) >>
  Cases_on `MEM bop [Add; Sub; Mul; Div; Mod]`
  >- binop_dispatch_tac binop_frag_arith_any >>
  Cases_on `MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]`
  >- binop_dispatch_tac binop_frag_unsafe_any >>
  Cases_on `bop = ShL \/ bop = ShR`
  >- binop_dispatch_tac binop_frag_shift_any >>
  Cases_on `bop = In \/ bop = NotIn`
  >- binop_dispatch_tac binop_frag_in_any >>
  binop_dispatch_tac binop_frag_rest_any
QED

Theorem binop_frag_typed:
  !ctx func cenv cx bop ann e1 e2 v1 v2 es0 tv1 tv2.
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    value_has_type tv1 v1 /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop (expr_type e1) ann
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE)
      [expr_type e1; expr_type e2] v1 v2 es0
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `expr_type e1`,
               `expr_type e2`, `if bop = Exp then expr_int_literal e1 else NONE`,
               `if bop = Exp then expr_int_literal e2 else NONE`,
               `[expr_type e1; expr_type e2]`, `v1`, `v2`, `es0`, `get_tenv cx`,
               `tv1`, `tv2`]
    mp_tac binop_frag_word_typed >>
  impl_tac >- asm_rewrite_tac[] >> simp[]
QED

Theorem expr_sim_pre_bop:
  !cenv cx env ann bop e1 e2 es.
    expr_sim_pre cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    expr_sim_pre cenv cx env e1 es /\
    !es'. expr_sim_inv cenv cx env es' ==> expr_sim_pre cenv cx env e2 es'
Proof
  rpt strip_tac
  >- gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_builtin_app_def]
  >- (drule expr_sim_pre_builtin_arg >> disch_then irule >>
      gvs[expr_sim_pre_def]) >>
  drule expr_sim_pre_builtin_arg >> disch_then irule >> simp[]
QED

Theorem expr_sim_ok_apply:
  !ctx func cenv cx env ty e es.
    expr_sim_ok cenv e /\ expr_sim_pre cenv cx env e es ==>
    expr_sim ctx func cenv cx ty e es
Proof
  metis_tac[expr_sim_ok_def]
QED

Theorem compile_bop_word_sim:
  !cenv ann bop e1 e2.
    expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2 /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) [e1; e2])
Proof
  rpt strip_tac >> simp[expr_sim_ok_def] >> rpt strip_tac >>
  drule expr_sim_pre_bop >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `expr_sim_pre cenv cx env e2 es` by (first_assum irule >> simp[]) >>
  `is_word_type (expr_type e1) /\ ~is_ArrayT (expr_type e1) /\
   ~is_bytestring_type (expr_type e1) /\
   is_word_type (expr_type e2) /\ ~is_ArrayT (expr_type e2) /\
   ~is_bytestring_type (expr_type e2)` by gvs[word_value_type_word] >>
  imp_res_tac well_typed_expr_type_evaluates >>
  `is_word_type ann` by (drule_all well_typed_binop_word_result >> simp[]) >>
  irule compile_bop_sim >> rpt conj_tac
  >~ [`binop_frag`]
  >- (rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`, `INL (Value v1)`, `es1`]
        mp_tac expr_sim_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `Value v1` mp_tac) >> simp[] >> strip_tac >>
      rename1 `value_has_type tv1 v1` >>
      `expr_sim_pre cenv cx env e2 es1` by (first_assum irule >> simp[]) >>
      conj_tac >- gvs[] >>
      conj_tac
      >- (rpt strip_tac >>
          qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1`, `INL tv`, `es2`] mp_tac
            expr_sim_pre_word_result >>
          impl_tac >- gvs[] >> strip_tac >> gvs[]) >>
      conj_tac
      >- metis_tac[expr_sim_ok_apply] >>
      rpt gen_tac >> strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e2`, `es1`, `INL (Value v2)`, `es2`]
        mp_tac expr_sim_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >>
      first_x_assum (qspec_then `Value v2` mp_tac) >> simp[] >>
      strip_tac >> rename1 `value_has_type tv2 v2` >> simp[] >>
      qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `e1`, `e2`,
                   `v1`, `v2`, `es2`, `tv1`, `tv2`] mp_tac binop_frag_typed >>
      impl_tac >- gvs[] >> simp[])
  >~ [`eval_expr cx e1 es = (INL _, _)`]
  >- (rpt strip_tac >>
      qspecl_then [`cenv`, `cx`, `env`, `e1`, `es`, `INL tv`, `es1`] mp_tac
        expr_sim_pre_word_result >>
      impl_tac >- gvs[] >> strip_tac >> gvs[])
  >~ [`compile_binop`]
  >- (rpt gen_tac >> strip_tac >> drule compile_binop_shape >> simp[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >> drule lower_value_word_shape >> gvs[])
  >~ [`lower_value`]
  >- (rpt gen_tac >> strip_tac >> drule lower_value_word_shape >> gvs[])
  >~ [`expr_sim`]
  >- metis_tac[expr_sim_ok_apply] >>
  gvs[]
QED

Theorem compile_bop_other_sim:
  !ctx func cenv cx env ty ann bop args es.
    expr_sim_below cenv (list_size expr_size args) /\
    expr_sim_pre cenv cx env (Builtin ann (Bop bop) args) es /\
    (!e1 e2. args = [e1; e2] ==>
             ~(word_value_type (expr_type e1) /\
               word_value_type (expr_type e2))) ==>
    expr_sim ctx func cenv cx ty (Builtin ann (Bop bop) args) es
Proof
  cheat
QED

Theorem compile_bop_case_sim:
  !cenv ann bop args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_sim_ok cenv (Builtin ann (Bop bop) args)
Proof
  rpt strip_tac >>
  Cases_on `?e1 e2. args = [e1; e2] /\ word_value_type (expr_type e1) /\
                    word_value_type (expr_type e2)`
  >- (pop_assum strip_assume_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      `expr_sim_ok cenv e1 /\ expr_sim_ok cenv e2` by
        metis_tac[expr_sim_below_mem, listTheory.MEM, expr_ok_def] >>
      irule compile_bop_word_sim >> fs[]) >>
  rw[expr_sim_ok_def] >> irule compile_bop_other_sim >>
  metis_tac[]
QED

(* A binary operator is lowered to a StackValue. *)
Theorem compile_bop_stack:
  !cenv ty ann bop args sa.
    ?t op sb. compile_expr cenv ty (Builtin ann (Bop bop) args) sa =
              (StackValue t op, sb)
Proof
  rpt gen_tac >>
  simp[compile_expr_bop, vyperASTTheory.expr_type_def] >>
  simp[Once compile_expr_def, LET_THM, as_stack_val_pair,
       pairTheory.UNCURRY] >>
  rw[] >>
  Cases_on `HD (TL args)` >>
  simp[pairTheory.UNCURRY] >>
  rename1 `Builtin _ bi _` >> Cases_on `bi` >> simp[]
QED

Theorem compile_bop_ok:
  !cenv ann bop args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_ok cenv (Builtin ann (Bop bop) args)
Proof
  rpt strip_tac >> irule expr_ok_stack >>
  simp[compile_bop_case_sim, compile_bop_stack] >>
  rpt strip_tac >> drule eval_expr_builtin_value >> simp[]
QED

(* ===== Unary operators ===== *)

Theorem compile_not_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Not args)
Proof
  cheat
QED

Theorem compile_neg_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Neg args)
Proof
  cheat
QED

Theorem compile_abs_sim:
  !cenv ann args.
    expr_sim_below cenv (list_size expr_size args) ==>
    expr_vv_ok cenv (Builtin ann Abs args)
Proof
  cheat
QED

(* ===== Conditional expression ===== *)

Theorem expr_sim_pre_ifexp:
  !cenv cx env t c a b es.
    expr_sim_pre cenv cx env (IfExp t c a b) es ==>
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    expr_sim_pre cenv cx env c es /\
    !es'. expr_sim_inv cenv cx env es' ==>
          expr_sim_pre cenv cx env a es' /\ expr_sim_pre cenv cx env b es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def] >> gvs[]
QED

(* A result of a word type is a value: an ArrayRef is typed by an array
   type, a HashMapRef by NoneTV. *)
Theorem word_type_toplevel_value:
  !t tenv tyv x.
    is_word_type t /\ evaluate_type tenv t = SOME tyv /\
    toplevel_value_typed x tyv ==>
    is_Value x
Proof
  Cases >> rw[is_word_type_def] >>
  TRY (rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_word_type_def]) >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_word_type_def]) >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  Cases_on `x` >> gvs[toplevel_value_typed_def]
QED

(* A ternary of a word type: compile_ifexp_vv_sim (exprSimIfExp), with the
   operands' shape from lower_value_word_shape (cheated). *)
Theorem compile_ifexp_word_sim:
  !cenv t c a b.
    expr_sim_below cenv (expr_size (IfExp t c a b)) /\ is_word_type t ==>
    expr_vv_ok cenv (IfExp t c a b)
Proof
  rw[expr_vv_ok_def] >> drule expr_sim_pre_ifexp >> strip_tac >>
  `expr_ok cenv c /\ expr_ok cenv a /\ expr_ok cenv b` by
    (fs[expr_sim_below_def] >> rpt conj_tac >> first_x_assum irule >>
     simp[vyperASTTheory.expr_size_def]) >>
  fs[expr_ok_def] >>
  simp[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  `expr_res_ok res` by
    (qspecl_then [`cenv`, `cx`, `env`, `IfExp t c a b`, `es`, `res`, `es'`]
       mp_tac expr_sim_pre_res_ok >> simp[] >> disch_then irule >>
     rpt strip_tac >>
     drule_all expr_sim_pre_eval >> strip_tac >>
     first_x_assum drule >>
     simp[expr_result_typed_def, expr_runtime_typed_def,
          vyperASTTheory.expr_type_def] >>
     metis_tac[word_type_toplevel_value]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `ty`, `t`, `c`, `a`, `b`, `es`]
    mp_tac compile_ifexp_vv_sim >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rpt gen_tac >> strip_tac >> drule lower_value_word_shape >>
          gvs[is_word_type_def])
      >- (rpt gen_tac >> strip_tac >> drule lower_value_word_shape >> gvs[])
      >- metis_tac[expr_sim_ok_def] >>
      rpt gen_tac >> strip_tac >> drule_all expr_sim_pre_eval >> strip_tac >>
      metis_tac[expr_sim_ok_def]) >>
  disch_then irule >> simp[]
QED

(* A ternary of an aggregate type, which supported_pure_expr admits for
   memory arrays, structs and strings (#561).  Cheated: compile_ifexp_vv_sim
   needs the compile-state shape of the branches' lower_value, which for a
   non-word type is #674's compile_expr_shape, and that gives neither
   cs_next_id's growth nor the shape under expr_sim_inv yet.  A ternary over
   storage or transient arrays has an ArrayRef result and a memory copy,
   which vv_holds relates through materialise; its branches' results are
   not expr_res_ok, so it needs their expr_vv_sim and unwrap_value's copy
   rather than their expr_sim (#575). *)
Theorem compile_ifexp_aggregate_sim:
  !cenv t c a b.
    expr_sim_below cenv (expr_size (IfExp t c a b)) /\ ~is_word_type t ==>
    expr_vv_ok cenv (IfExp t c a b)
Proof
  cheat
QED

Theorem compile_ifexp_sim:
  !cenv ann c e1 e2.
    expr_sim_below cenv (expr_size (IfExp ann c e1 e2)) ==>
    expr_vv_ok cenv (IfExp ann c e1 e2)
Proof
  metis_tac[compile_ifexp_word_sim, compile_ifexp_aggregate_sim]
QED
