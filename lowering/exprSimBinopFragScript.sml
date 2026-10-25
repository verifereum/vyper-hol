(*
 * Expression simulation: binary operators on typed word operands (#636,
 * Operators)
 *
 * binop_frag_typed, the fragment of a binary operator on operands of
 * word_value_types that have their types, by the operator's group onto the
 * simulation lemmas of exprSimOps, exprSimCompare and exprSimArith.
 *
 * TOP-LEVEL:
 *   binop_frag_typed      — binop_frag at the operands' types, for
 *                           exprSimOperators' compile_bop_word_sim
 *   binop_frag_word_typed — the same over any typed word operands
 *
 * Cheated, the operators those lemmas do not cover:
 *   binop_frag_pow        — ** and pow_mod (#572)
 *   binop_frag_shift_572  — << of an integer narrower than 256 bits, and
 *                           shifts by a negative amount (#572)
 *   binop_frag_shr_narrow — >> of an integer narrower than 256 bits, which
 *                           the lowering gets right but compile_shift_sim
 *                           does not cover
 *   binop_frag_unsafe_width — unsafe arithmetic on integer widths that
 *                           aren't whole bytes, which Vyper does not have
 *)

Theory exprSimBinopFrag
Ancestors
  list finite_map
  fragExec exprSim exprSimHyps exprSimOps exprSimCompare exprSimArith
  exprBopLowering loweringSlice
  exprLowering compileEnv
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTyping vyperTypeInvariants vyperTypeExprResult vyperTypeExprSoundness

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

(* The operators whose lowering #692's lemmas do not cover, each on typed
   operands, cheated.

   The cases #572 tracks, where the lowering does not compute the source's
   result: ** (compile_safe_pow's EXP wraps where the source reverts unless
   an operand is a literal) and pow_mod (ExpMod falls through compile_binop
   to INVALID). *)
Theorem binop_frag_pow:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = Exp \/ bop = ExpMod) /\ well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* Also #572: << of an integer narrower than 256 bits, which the lowering
   does not truncate, and a shift by a negative amount, where the source
   raises and the lowering shifts.  Vyper rejects shifts of types other than
   int256 and uint256; well_typed_binop admits every integer type. *)
Theorem binop_frag_shift_572:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\
    (bop = ShL /\ type_bits t1 < 256 \/ ?i. v2 = IntV i /\ i < 0) /\
    well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* >> of an integer narrower than 256 bits by a non-negative amount.  The
   lowering computes the source's result here (SHR or SAR of the operand's
   word), but compile_shift_sim is for 256-bit integers only. *)
Theorem binop_frag_shr_narrow:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = ShR /\ type_bits t1 < 256 /\ ~(?i. v2 = IntV i /\ i < 0) /\
    well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* The wrapping operators on an integer type whose width is not a whole
   number of bytes, which evaluate_type admits but Vyper does not have.  For
   a signed type wrap_truncate sign-extends from a byte boundary, as Python
   does, so the lowering does not compute the source's result; for an
   unsigned one its mask is right, but compile_unsafe_sim is for widths of
   whole bytes only. *)
Theorem binop_frag_unsafe_width:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    type_bits t1 MOD 8 <> 0 /\ well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  cheat
QED

(* Instantiates a dispatch lemma at the current goal's variables and
   discharges its premises from the assumptions. *)
fun binop_dispatch_tac th =
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `t1`, `t2`, `bl`,
               `el`, `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`, `tv2`]
    mp_tac th >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >>
  simp[];

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
  >- binop_dispatch_tac binop_frag_unsafe_width >>
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
  Cases_on `bop = ShL /\ type_bits t1 < 256 \/ ?i. v2 = IntV i /\ i < 0`
  >- binop_dispatch_tac binop_frag_shift_572 >>
  Cases_on `bop = ShR /\ type_bits t1 < 256`
  >- binop_dispatch_tac binop_frag_shr_narrow >>
  `~(type_bits t1 < 256)` by
    (qpat_x_assum `bop = ShL \/ bop = ShR` strip_assume_tac >> fs[]) >>
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
  >- binop_dispatch_tac binop_frag_pow >>
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

