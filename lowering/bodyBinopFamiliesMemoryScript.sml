(* The binary operators' fragments on the memory-checked path: S1's
   per-operator binop_frag lemmas (exprSimArith, exprSimCompare,
   exprBopBitwise, exprBopFlag, exprBopShift, exprSimBinopFrag) restated for
   binop_frag_val_mem.  Every one of them reaches its fragment through
   binop_frag_straight, whose memory twin binop_frag_val_mem_straight
   (from bodyBinopFragMemory's binop_frag_mem_straight) takes the same
   straight-line run, so the proofs are S1's with that lemma swapped in. *)
Theory bodyBinopFamiliesMemory
Ancestors
  bodyBinopFragMemory
  exprSimBinopFrag exprSimArith exprSimCompare exprBopBitwise exprBopFlag
  exprBopShift exprBopStraight exprBopSimDefs exprBopSimProps exprSimBopTyped
  exprSimOps exprSimHyps exprSimHypsDefs exprSimProps exprSimDefs
  primeFactor freshWrites fragGasFresh fragExec varsExt loweringPosts
  arithmeticProps builtinMath builtinProps builtinSimple vyperArith
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprBopLowering loweringSlice exprLowering compileEnv exprLoweringProps
  emitHelper emitHelperProps
  vyperAST vyperInterpreter vyperState vyperContext vyperTypeSystem
  vyperTypeCallGraph vyperTyping vyperTypeInvariants vyperTypeExprResult
  vyperTypeExprSoundness vyperValue vyperValueOperation valueEncoding
  venomExecSemantics venomInst venomState
  arithmetic list rich_list finite_map pred_set fcp bit
  integer integer_word int_bitwise intBits words
Libs
  emitTacticsLib intLib pairLib

(* binop_frag (exprBopSimDefs) on the memory-checked path: the operands
   held in their plain words. *)
Definition binop_frag_val_mem_def:
  binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0 <=>
    binop_frag_mem ctx func cenv cx bop ty ann bl el tys v1 v2
      (val_to_w256 v1) (val_to_w256 v2) es0
End

(* binop_frag_straight (exprBopStraight) for binop_frag_val_mem. *)
Theorem binop_frag_val_mem_straight:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0.
    (!x y. straight_fresh (compile_binop bop x y ty bl el)) /\
    (expr_res_ok (bop_result cx ann bop tys v1 v2 es0) ==>
     (?v. bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) /\
            eval_operand y ss = SOME (val_to_w256 v2) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
                  eval_operand op ss' = SOME (val_to_w256 v)) \/
     (?m. bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError m)) /\
          !x y sa sb op ss.
            compile_binop bop x y ty bl el sa = (op, sb) /\
            fresh_vars_wrt sa ss /\
            eval_operand x ss = SOME (val_to_w256 v1) /\
            eval_operand y ss = SOME (val_to_w256 v2) ==>
            ?ss'. run_inst_seq (emitted_insts sa sb) ss =
                    Abort Revert_abort ss')) ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rewrite_tac[binop_frag_val_mem_def] >> rpt strip_tac >>
  irule binop_frag_mem_straight >> asm_rewrite_tac[]
QED

(* From exprSimCompare: compile_compare_words_sim, through
   binop_frag_mem_straight. *)
Theorem compile_compare_words_sim_mem:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
    (expr_res_ok (bop_result cx ann bop tys v1 v2 es0) ==>
     bop_result cx ann bop tys v1 v2 es0 =
       INL (BoolV (eval_compare bop ty w1 w2))) ==>
    binop_frag_mem ctx func cenv cx bop ty ann bl el tys v1 v2 w1 w2 es0
Proof
  rpt gen_tac >> strip_tac >> irule binop_frag_mem_straight >>
  conj_tac >- metis_tac[straight_fresh_compare] >>
  strip_tac >> disj1_tac >>
  qexists_tac `BoolV (eval_compare bop ty w1 w2)` >>
  simp[word_value_def] >> rpt strip_tac >>
  `compile_compare bop x y ty sa = (op, sb)` by
    (qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >> fs[] >>
     rw[compile_binop_def]) >>
  qspecl_then [`bop`, `x`, `y`, `ty`, `ss`, `sa`, `op`, `sb`,
               `w1`, `w2`] mp_tac compile_compare_correct >>
  simp[] >> strip_tac >> qexists_tac `ss'` >> simp[] >>
  Cases_on `eval_compare bop ty w1 w2` >>
  gvs[val_to_w256_def, bool_to_word_def]
QED

(* From exprSimArith. *)
(* binop_frag_val_mem for the wrapping operators on two integers of a type of b
   bits, b a multiple of 8, the second within the type's bound. *)
Theorem compile_unsafe_sim_mem:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed (type_bits ty)
            else Unsigned (type_bits ty)) /\
    0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
    within_int_bound
      (if is_signed_type ty then Signed (type_bits ty)
       else Unsigned (type_bits ty)) i2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `v1`, `v2`, `es0`, `i1`, `i2`,
               `type_bits ty`] mp_tac bop_result_unsafe >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  match_mp_tac binop_frag_val_mem_straight >> conj_tac
  >- (rpt gen_tac >> irule straight_fresh_unsafe >> first_assum ACCEPT_TAC) >>
  strip_tac >> disj1_tac >> qexists_tac `v` >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_binop_unsafe] >> strip_tac >>
  irule compile_unsafe_binop_correct >>
  goal_assum (drule_at (Pat `compile_unsafe_binop`)) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule step_unsafe_opcode >> asm_rewrite_tac[]
QED

(* From exprSimArith. *)
(* binop_frag_val_mem for a checked add, sub or mul of two integers of an integer
   type, within its bound: the result when it is within the bound, a revert
   when it is not. *)
Theorem compile_checked_sim_mem:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2 u.
    MEM bop [Add; Sub; Mul] /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qabbrev_tac `rr = if bop = Add then i1 + i2 else if bop = Sub then i1 - i2
                   else i1 * i2` >>
  `bop_result cx ann bop tys (IntV i1) (IntV i2) es0 =
     if within_int_bound u rr then INL (IntV rr)
     else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (qspecl_then [`cx`, `ann`, `bop`, `IntV i1`, `IntV i2`, `es0`, `i1`, `i2`,
                  `u`] mp_tac bop_result_checked >> simp[Abbr `rr`]) >>
  `!x y sa sb op ss.
     compile_binop bop x y ty bl el sa = (op, sb) /\
     fresh_vars_wrt sa ss /\ eval_operand x ss = SOME (i2w i1) /\
     eval_operand y ss = SOME (i2w i2) ==>
     (within_int_bound u rr ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
            eval_operand op ss' = SOME (i2w rr)) /\
     (~within_int_bound u rr ==>
      ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')` by
    (rpt gen_tac >> strip_tac >> fs[] >> gvs[compile_binop_def, Abbr `rr`]
     >- (irule compile_safe_add_run >> metis_tac[])
     >- (irule compile_safe_sub_run >> metis_tac[]) >>
     irule compile_safe_mul_run >> metis_tac[]) >>
  match_mp_tac binop_frag_val_mem_straight >> conj_tac
  >- (rpt gen_tac >> fs[] >> simp[compile_binop_def, straight_fresh_checked]) >>
  strip_tac >> asm_rewrite_tac[val_to_w256_def] >>
  Cases_on `within_int_bound u rr` >> asm_rewrite_tac[]
  >- (disj1_tac >> qexists_tac `IntV rr` >>
      rewrite_tac[val_to_w256_def, word_value_def] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `"bounded_int_op bound"` >> rewrite_tac[] >>
  metis_tac[]
QED

(* From exprSimArith. *)
(* Checked Div/Mod (non-decimal): both sides fail together on a zero divisor
   or signed INT_MIN / -1, and otherwise agree via the EVM safe_* ops. *)
Theorem compile_divmod_sim_mem:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2 u.
    MEM bop [Div; Mod] /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
    0 < type_bits ty /\ type_bits ty <= 256 /\
    within_int_bound u i1 /\ within_int_bound u i2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qspecl_then [`ty`, `u`] mp_tac type_to_int_bound_bits >> simp[] >>
  strip_tac >>
  `math_val ty (i2w i1 : bytes32) = i1 /\ math_val ty (i2w i2 : bytes32) = i2`
    by gvs[math_val_i2w] >>
  `i2 = 0 <=> i2w i2 = (0w : bytes32)` by
    (eq_tac >> strip_tac >- simp[integer_wordTheory.i2w_0] >>
     qspecl_then [`type_bits ty`, `is_signed_type ty`, `i2`] mp_tac
       i2w_eq_0_within >> gvs[]) >>
  match_mp_tac binop_frag_val_mem_straight >> conj_tac
  >- (rpt gen_tac >> fs[] >> gvs[compile_binop_def, straight_fresh_checked]) >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `IntV i1`, `IntV i2`, `es0`, `i1`,
               `i2`, `u`] mp_tac bop_result_divmod >> impl_tac >- simp[] >>
  qmatch_goalsub_abbrev_tac `(BAD ==> _) /\ _ ==> _` >>
  Cases_on `BAD` >> simp[] >> strip_tac
  >- ((* zero divisor or signed overflow: the lowering reverts *)
      disj2_tac >> qexists_tac `m` >> asm_rewrite_tac[val_to_w256_def] >>
      rpt strip_tac >> fs[markerTheory.Abbrev_def] >>
      gvs[compile_binop_def, integer_wordTheory.i2w_0]
      >- metis_tac[compile_safe_div_by_zero]
      >- (gvs[math_val_def] >> irule compile_safe_div_overflow >>
          simp[] >> metis_tac[]) >>
      metis_tac[compile_safe_mod_by_zero]) >>
  (* defined result: the lowering computes the matching safe_* word *)
  disj1_tac >> qexists_tac `IntV z` >>
  rewrite_tac[val_to_w256_def, word_value_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> fs[markerTheory.Abbrev_def] >>
  `in_type_range ty i1` by gvs[in_type_range_within] >>
  gvs[compile_binop_def]
  >- (qspecl_then [`x`, `y`, `ty`, `ss`, `sa`, `op`, `sb`, `i2w i1`,
                   `i2w i2`] mp_tac compile_safe_div_ok >>
      impl_tac >- (Cases_on `is_signed_type ty` >> gvs[math_val_def]) >>
      Cases_on `is_signed_type ty` >> simp[]) >>
  qspecl_then [`x`, `y`, `ty`, `ss`, `sa`, `op`, `sb`, `i2w i1`, `i2w i2`]
    mp_tac compile_safe_mod_correct >>
  Cases_on `is_signed_type ty` >> gvs[]
QED

(* From exprSimArith. *)
(* Decimals lower as 168-bit signed integers: where the lowering emits the
   int168 code and the source result differs only in DecimalV vs IntV (with
   runtime errors matched), the int168 operator fragment carries over. *)
Theorem binop_frag_decimal_transfer_mem:
  !ctx func cenv cx bop ann ann' bl el d1 d2 es0.
    binop_frag_val_mem ctx func cenv cx bop (BaseT (IntT 168)) ann' bl el tys
      (IntV d1) (IntV d2) es0 /\
    (!x y. compile_binop bop x y (BaseT DecimalT) bl el =
           compile_binop bop x y (BaseT (IntT 168)) bl el) /\
    ((?z. bop_result cx ann' bop tys (IntV d1) (IntV d2) es0 =
            INL (IntV z) /\
          bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es0 =
            INL (DecimalV z)) \/
     (?m m'. bop_result cx ann' bop tys (IntV d1) (IntV d2) es0 =
               INR (Error (RuntimeError m)) /\
             bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es0 =
               INR (Error (RuntimeError m')))) ==>
    binop_frag_val_mem ctx func cenv cx bop (BaseT DecimalT) ann bl el tys
      (DecimalV d1) (DecimalV d2) es0
Proof
  rpt gen_tac >> simp[binop_frag_val_mem_def, binop_frag_mem_def] >> strip_tac >> rpt gen_tac >>
  strip_tac >>
  first_x_assum (qspecl_then [`sa`, `sb`, `x`, `y`, `op`, `s0`] mp_tac) >>
  (impl_tac >- gvs[expr_res_ok_def, val_to_w256_def]) >>
  strip_tac >> qexists_tac `r` >> asm_rewrite_tac[] >>
  gvs[val_to_w256_def, word_value_def] >>
  Cases_on `r` >> gvs[expr_exit_def]
QED

(* From exprSimArith. *)
Theorem compile_decimal_add_sub_mod_sim_mem:
  !ctx func cenv cx bop ann bl el d1 d2 es0.
    MEM bop [Add; Sub; Mod] /\
    within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 ==>
    binop_frag_val_mem ctx func cenv cx bop (BaseT DecimalT) ann bl el tys
      (DecimalV d1) (DecimalV d2) es0
Proof
  rpt strip_tac >> irule binop_frag_decimal_transfer_mem >>
  conj_tac
  >- (fs[] >> rpt gen_tac >>
      simp[compile_binop_def, compile_safe_add_def, compile_safe_sub_def,
           compile_safe_mod_def, clamp_and_return_def, compile_clamp_def,
           type_bounds_def, type_bits_def, is_signed_type_def]) >>
  qexists_tac `BaseT (IntT 168)` >> conj_tac
  >- (fs[] >>
      simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
           bounded_int_op_def, bounded_decimal_op_def, type_to_int_bound_def,
           int_bound_bits_def] >> rw[]) >>
  `bop = Add \/ bop = Sub \/ bop = Mod` by fs[] >>
  FIRST (map (fn th => irule th >>
                       simp[type_to_int_bound_def, type_bits_def] >> NO_TAC)
              [compile_checked_sim_mem, compile_divmod_sim_mem])
QED

(* From exprSimArith. *)
Theorem compile_decimal_mul_div_sim_mem:
  !ctx func cenv cx bop ann bl el d1 d2 es0.
    MEM bop [Mul; Div] /\
    within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 ==>
    binop_frag_val_mem ctx func cenv cx bop (BaseT DecimalT) ann bl el tys
      (DecimalV d1) (DecimalV d2) es0
Proof
  rpt strip_tac >> irule binop_frag_val_mem_straight >> conj_tac
  >- (fs[] >> rpt gen_tac >>
      simp[compile_binop_def, is_decimal_type_def, decimal_divisor_def,
           straight_fresh_checked, straight_fresh_decimal_div]) >>
  strip_tac >>
  `in_type_range (BaseT DecimalT) d1 /\ in_type_range (BaseT DecimalT) d2` by
    simp[in_type_range_decimal] >>
  `bop = Mul \/ bop = Div` by fs[] >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       decimal_sgn_quot, bounded_decimal_op_def, compile_binop_def,
       is_decimal_type_def, decimal_divisor_def, val_to_w256_def]
  >- ((* Mul: truncating product, bounded to 168 bits *)
      Cases_on `within_int_bound (Signed 168) (d1 * d2 quot 10000000000)` >>
      simp[word_value_def, val_to_w256_def] >> rpt strip_tac >>
      qspecl_then [`x`, `y`, `ss`, `sa`, `op`, `sb`, `d1`, `d2`] mp_tac
        compile_safe_decimal_mul_run >>
      gvs[in_type_range_decimal]) >>
  (* Div: the scaled dividend over the divisor, after the zero check *)
  `w2i (i2w d1 : bytes32) = d1 /\ w2i (i2w d2 : bytes32) = d2` by
    (conj_tac >> irule integer_wordTheory.w2i_i2w >>
     fs[vyperValueTheory.within_int_bound_def, wordsTheory.INT_MIN_def,
        wordsTheory.INT_MAX_def, wordsTheory.dimword_def] >>
     intLib.ARITH_TAC) >>
  `(i2w d1 * n2w 10000000000 : bytes32) = i2w (d1 * 10000000000)` by
    (qspecl_then [`i2w d1 : bytes32`, `n2w 10000000000 : bytes32`] mp_tac
       integer_wordTheory.word_mul_i2w >>
     asm_rewrite_tac[w2i_decimal_divisor] >>
     disch_then (SUBST1_TAC o SYM) >> REFL_TAC) >>
  `(i2w d2 = (0w : bytes32)) <=> d2 = 0` by
    (eq_tac >> strip_tac >> simp[integer_wordTheory.i2w_0] >>
     qpat_x_assum `w2i (i2w d2) = d2` (SUBST1_TAC o SYM) >>
     asm_simp_tac std_ss [integer_wordTheory.word_0_w2i]) >>
  Cases_on `d2 = 0` >> simp[]
  >- (rpt strip_tac >>
      qspecl_then [`x`, `y`, `ss`, `sa`, `op`, `sb`, `i2w d1`, `i2w d2`]
        mp_tac compile_safe_decimal_div_run >> gvs[]) >>
  `safe_sdiv (i2w d1 * n2w 10000000000) (i2w d2) =
     (i2w (d1 * 10000000000) / i2w d2 : bytes32)` by
    asm_simp_tac std_ss [safe_sdiv_def] >>
  Cases_on `within_int_bound (Signed 168)
              (w2i (i2w (d1 * 10000000000) / i2w d2 : bytes32))` >>
  simp[word_value_def, val_to_w256_def, integer_wordTheory.i2w_w2i] >>
  rpt strip_tac >>
  qspecl_then [`x`, `y`, `ss`, `sa`, `op`, `sb`, `i2w d1`, `i2w d2`] mp_tac
    compile_safe_decimal_div_run >>
  gvs[in_type_range_decimal]
QED

(* From exprSimCompare. *)
(* binop_frag_val_mem for the comparisons, on two word values of one type. *)
Theorem compile_compare_sim_mem:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 tv.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
    word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
    (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
    (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
         m <= 256) ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[binop_frag_val_mem_def] >>
  irule compile_compare_words_sim_mem >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `tv`, `v1`, `v2`, `es0`] mp_tac
    bop_result_compare >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_then ACCEPT_TAC
QED

(* From exprSimCompare. *)
(* binop_frag_val_mem for Min and Max, on two word values of one type. *)
Theorem compile_minmax_sim_mem:
  !ctx func cenv cx mm ty ann bl el v1 v2 es0 tv.
    (mm = Min \/ mm = Max) /\
    word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
    (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
    (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
         m <= 256) ==>
    binop_frag_val_mem ctx func cenv cx mm ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  match_mp_tac binop_frag_val_mem_straight >> conj_tac
  >- (rpt gen_tac >> metis_tac[straight_fresh_minmax]) >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `mm`, `ty`, `tv`, `v1`, `v2`, `es0`] mp_tac
    bop_result_minmax >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> asm_rewrite_tac[] >> rpt strip_tac >>
  qspecl_then [`mm`, `x`, `y`, `ty`, `bl`, `el`, `sa`, `op`, `sb`,
               `val_to_w256 v1`, `val_to_w256 v2`, `ss`] mp_tac
    compile_minmax_correct >>
  asm_simp_tac bool_ss []
QED

(* From exprSimCompare. *)
(* binop_frag_mem for == and != on two address or two bytesN values of
   one type, held in their typed words: compile_compare's EQ on the words
   is the source's comparison of the bytes. *)
Theorem compile_compare_bytes_sim_mem:
  !ctx func cenv cx bop ty ann bl el tys tv b1 b2 es0.
    (bop = Eq \/ bop = NotEq) /\
    (tv = BaseTV AddressT \/ ?m. tv = BaseTV (BytesT (Fixed m)) /\ m <= 32) /\
    value_has_type tv (BytesV b1) /\ value_has_type tv (BytesV b2) ==>
    binop_frag_mem ctx func cenv cx bop ty ann bl el tys
      (BytesV b1) (BytesV b2)
      (typed_val_to_w256 tv (BytesV b1)) (typed_val_to_w256 tv (BytesV b2)) es0
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `w1 = typed_val_to_w256 tv (BytesV b1)` >>
  qabbrev_tac `w2 = typed_val_to_w256 tv (BytesV b2)` >>
  `(w1 = w2 <=> b1 = b2)` by
    (unabbrev_all_tac >> irule typed_val_to_w256_bytes_11 >> simp[]) >>
  irule compile_compare_words_sim_mem >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      binop_negate_def, eval_compare_def]
QED

(* From exprBopBitwise. *)
(* The lowering emits the word operation, one instruction. *)
Theorem compile_bitwise_sim_mem:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0.
    (bop = And \/ bop = Or \/ bop = XOr) /\
    (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
       within_int_bound
         (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  irule binop_frag_val_mem_straight >>
  conj_tac >- metis_tac[straight_fresh_compile_bitwise] >>
  disch_tac >>
  drule_all bop_result_bitwise >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  rpt strip_tac >>
  drule_all compile_bitwise_run >> simp[]
QED

(* From exprBopFlag. *)
(* binop_frag_val_mem for In and NotIn on two flags of a tys type with at most 256
   members. *)
Theorem compile_flag_in_sim_mem:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 m.
    (bop = In \/ bop = NotIn) /\
    value_has_type (FlagTV m) v1 /\ value_has_type (FlagTV m) v2 /\
    m <= 256 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  match_mp_tac binop_frag_val_mem_straight >> conj_tac
  >- (rpt gen_tac >> metis_tac[straight_fresh_flag_in]) >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `m`, `v1`, `v2`, `es0`] mp_tac
    bop_result_flag_in >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  disj1_tac >> simp[word_value_def] >> rpt strip_tac >>
  qspecl_then [`bop`, `x`, `y`, `ty`, `bl`, `el`, `sa`, `op`, `sb`,
               `val_to_w256 v1`, `val_to_w256 v2`, `ss`] mp_tac
    compile_flag_in_correct >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `ss'` >> asm_rewrite_tac[] >>
  Cases_on `if bop = In then val_to_w256 v1 && val_to_w256 v2 <> 0w
            else val_to_w256 v1 && val_to_w256 v2 = 0w` >>
  simp[val_to_w256_def, bool_to_word_def]
QED

(* From exprBopShift. *)
(* binop_frag_val_mem for ShL and ShR of a 256-bit integer by a uint256 amount:
   one instruction. *)
Theorem compile_shift_sim_mem:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2.
    (bop = ShL \/ bop = ShR) /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    within_int_bound (Unsigned 256) i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed 256 else Unsigned 256) /\
    within_int_bound (if is_signed_type ty then Signed 256 else Unsigned 256)
      i1 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  irule binop_frag_val_mem_straight >>
  (conj_tac >- metis_tac[straight_fresh_compile_shift]) >>
  disch_tac >>
  `?v. bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
       val_to_w256 v =
         if bop = ShL then word_lsl (val_to_w256 v1) (w2n (val_to_w256 v2))
         else if is_signed_type ty
         then word_asr (val_to_w256 v1) (w2n (val_to_w256 v2))
         else word_lsr (val_to_w256 v1) (w2n (val_to_w256 v2))`
    by (irule bop_result_shift >> simp[]) >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) compile_shift_run >>
  disch_then (qspecl_then [`ss`, `val_to_w256 v1`, `val_to_w256 v2`] mp_tac) >>
  simp[]
QED

(* From exprSimBinopFrag. *)
(* Checked + - * / % on two integers of one type. *)
Theorem binop_frag_int_arith_mem:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ is_int_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  Cases_on `bop` >> fs[]
  >~ [`binop_frag_val_mem _ _ _ _ Div`] >- (irule compile_divmod_sim_mem >> simp[])
  >~ [`binop_frag_val_mem _ _ _ _ Mod`] >- (irule compile_divmod_sim_mem >> simp[]) >>
  irule compile_checked_sim_mem >> simp[]
QED

(* From exprSimBinopFrag. *)
(* Checked + - * / % on two decimals. *)
Theorem binop_frag_decimal_arith_mem:
  !ctx func cenv cx bop bl el tys v1 v2 es0 tenv tv.
    MEM bop [Add; Sub; Mul; Div; Mod] /\
    evaluate_type tenv (BaseT DecimalT) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop (BaseT DecimalT) (BaseT DecimalT) bl el
      tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `tv`, `v1`] mp_tac decimal_type_value >>
  qspecl_then [`tenv`, `tv`, `v2`] mp_tac decimal_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  Cases_on `MEM bop [Mul; Div]`
  >- (irule compile_decimal_mul_div_sim_mem >> simp[]) >>
  irule compile_decimal_add_sub_mod_sim_mem >> simp[] >>
  Cases_on `bop` >> fs[]
QED

(* From exprSimBinopFrag. *)
(* The wrapping operators on two integers of one type of a whole number of
   bytes. *)
Theorem binop_frag_unsafe_typed_mem:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    is_int_type ty /\ type_bits ty MOD 8 = 0 /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  irule compile_unsafe_sim_mem >> simp[]
QED

(* From exprSimBinopFrag. *)
(* The comparisons, min and max on two word values of one type. *)
Theorem binop_frag_compare_typed_mem:
  !ctx func cenv cx bop ty ann bl el tys v1 v2 es0 tenv tv.
    MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
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
  >- (irule compile_minmax_sim_mem >> metis_tac[]) >>
  irule compile_compare_sim_mem >> gvs[] >> metis_tac[]
QED

(* From exprSimBinopFrag. *)
(* & | ^ on two word values of one type. *)
Theorem binop_frag_bitwise_typed_mem:
  !ctx func cenv cx bop ty bl el tys v1 v2 es0 tenv tv.
    (bop = And \/ bop = Or \/ bop = XOr) /\ word_value_type ty /\
    evaluate_type tenv ty = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> irule compile_bitwise_sim_mem >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac word_value_type_value_cases >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac word_value_type_value_cases >>
  asm_rewrite_tac[] >> rpt strip_tac >> gvs[type_to_int_bound_def]
QED

(* From exprSimBinopFrag. *)
(* Flag membership on two flags of one type. *)
Theorem binop_frag_flag_in_typed_mem:
  !ctx func cenv cx bop nsid ty ann bl el tys v1 v2 es0 tenv tv.
    (bop = In \/ bop = NotIn) /\
    evaluate_type tenv (FlagT nsid) = SOME tv /\
    value_has_type tv v1 /\ value_has_type tv v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  irule compile_flag_in_sim_mem >> metis_tac[]
QED

(* From exprSimBinopFrag. *)
(* << and >> on a 256-bit integer by a non-negative amount. *)
Theorem binop_frag_shift_typed_mem:
  !ctx func cenv cx bop ty t2 bl el tys v1 v2 es0 tenv tv1 tv2 i2.
    (bop = ShL \/ bop = ShR) /\ is_int_type ty /\ type_bits ty = 256 /\
    is_int_type t2 /\ v2 = IntV i2 /\ 0 <= i2 /\
    evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop ty ty bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`tenv`, `ty`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `within_int_bound (Unsigned 256) i2` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  irule compile_shift_sim_mem >> gvs[]
QED

(* From exprSimBinopFrag. *)
(* Power guards reflect source bounds when literal metadata agrees with
   the typed operands.  A base literal or nonnegative exponent literal is
   required; the emitted ASSERT rejects negative exponents and overflow. *)
Theorem binop_frag_pow_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = Exp /\ well_typed_binop ann bop t1 t2 /\
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_tac >>
  `is_int_type t1 /\ is_int_type t2` by gvs[well_typed_binop_def] >>
  qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[well_typed_binop_def] >>
  (rename1 `binop_frag_val_mem _ _ _ _ Exp _ _ _ _ _ (IntV a) (IntV b) _` >>
  `type_bits ann MOD 8 = 0` by metis_tac[int_type_byte_width] >>

  drule_then assume_tac bop_result_power >>
  irule binop_frag_val_mem_straight >> conj_tac
  >- simp[compile_binop_def, straight_fresh_compile_safe_pow] >>
  simp[] >>
  Cases_on `b < 0`
  >- (simp[] >> strip_tac >>
      rpt gen_tac >> simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
      drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >> simp[] >>
      `~(0 <= b)` by intLib.ARITH_TAC >> metis_tac[]) >>
  Cases_on `within_int_bound
    (if is_signed_type ann then Signed (type_bits ann) else Unsigned (type_bits ann))
    (a ** Num b)`
  >- (simp[word_value_def] >> strip_tac >> rpt gen_tac >>
      simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
      drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >> simp[] >>
      `0 <= b` by intLib.ARITH_TAC >> metis_tac[]) >>
  simp[] >> strip_tac >>
  rpt gen_tac >> simp[compile_binop_def, valueEncodingTheory.val_to_w256_def] >> strip_tac >>
  drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >> simp[] >> metis_tac[])
QED

(* From exprSimBinopFrag. *)
(* Right-shift arithmetic at genuinely narrow widths, independent of any
   checker restriction: signed and unsigned encodings widen safely to 256 bits. *)
Theorem binop_frag_shr_narrow_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    bop = ShR /\ type_bits t1 < 256 /\ ~(?i. v2 = IntV i /\ i < 0) /\
    ann = t1 /\ is_int_type t1 /\ is_int_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[] >>
  rename1 `value_has_type tv2 (IntV i2)` >>
  `0 <= i2` by intLib.ARITH_TAC >>
  `within_int_bound (Unsigned 256) i2` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  `type_bits ann <= 256` by decide_tac >>
  `?v. bop_result cx ann ShR tys (IntV i) (IntV i2) es0 = INL v /\
       word_value v /\ val_to_w256 v =
         (if is_signed_type ann
          then word_asr (val_to_w256 (IntV i)) (w2n (val_to_w256 (IntV i2)))
          else word_lsr (val_to_w256 (IntV i)) (w2n (val_to_w256 (IntV i2))))` by
    (irule bop_result_shr >> simp[] >>
     qexists_tac `type_bits ann` >> simp[]) >>
  irule binop_frag_val_mem_straight >>
  (conj_tac >- metis_tac[straight_fresh_compile_shift]) >>
  disch_tac >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`) compile_shift_run >>
  disch_then (qspecl_then [`ss`, `val_to_w256 (IntV i)`, `val_to_w256 (IntV i2)`] mp_tac) >>
  simp[]
QED

(* From exprSimBinopFrag. *)
(* Accepted shifts retain the nonnegative evaluated amount.  ShL is
   full-width; ShR also uses the independently proved narrow arithmetic. *)
Theorem binop_frag_shift_572_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ (?i. v2 = IntV i /\ 0 <= i) /\
    well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >> gvs[well_typed_binop_def]
  >- (irule binop_frag_shift_typed_mem >> simp[is_int_type_def, type_bits_def] >>
      metis_tac[])
  >- (irule binop_frag_shift_typed_mem >> simp[is_int_type_def, type_bits_def] >>
      metis_tac[]) >>
  `type_bits ann <= 256` by
    (qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
     simp[] >> metis_tac[]) >>
  Cases_on `type_bits ann = 256`
  >- (irule binop_frag_shift_typed_mem >> simp[] >> metis_tac[]) >>
  irule binop_frag_shr_narrow_mem >> simp[] >>
  `type_bits ann < 256` by decide_tac >> metis_tac[integerTheory.INT_NOT_LE]
QED

(* From exprSimBinopFrag. *)
fun binop_dispatch_mem_tac th =
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ann`, `t1`, `t2`, `bl`,
               `el`, `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`, `tv2`]
    mp_tac th >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >>
  simp[];

(* From exprSimBinopFrag. *)
(* Each operator on typed operands of word_value_types, by its group. *)
Theorem binop_frag_arith_any_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [Add; Sub; Mul; Div; Mod] /\ well_typed_binop ann bop t1 t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_numeric_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  Cases_on `ann = BaseT DecimalT`
  >- (pop_assum SUBST_ALL_TAC >> irule binop_frag_decimal_arith_mem >>
      metis_tac[]) >>
  irule binop_frag_int_arith_mem >> gvs[] >> metis_tac[]
QED

(* From exprSimBinopFrag. *)
Theorem binop_frag_unsafe_any_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
    well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_int_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  irule binop_frag_unsafe_typed_mem >> metis_tac[]
QED

(* From exprSimBinopFrag. *)
Theorem binop_frag_shift_any_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = ShL \/ bop = ShR) /\ well_typed_binop ann bop t1 t2 /\
    (?i. v2 = IntV i /\ 0 <= i) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  binop_dispatch_mem_tac binop_frag_shift_572_mem
QED

(* From exprSimBinopFrag. *)
Theorem binop_frag_in_any_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    (bop = In \/ bop = NotIn) /\ well_typed_binop ann bop t1 t2 /\
    word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  `?nsid. t1 = FlagT nsid /\ t2 = FlagT nsid` by
    (Cases_on `t2` >> gvs[well_typed_binop_def, word_value_type_def]) >>
  gvs[] >> irule binop_frag_flag_in_typed_mem >> metis_tac[]
QED

(* From exprSimBinopFrag. *)
Theorem binop_frag_rest_any_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    MEM bop [And; Or; XOr; Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\
    well_typed_binop ann bop t1 t2 /\ word_value_type t1 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
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
        mp_tac binop_frag_bitwise_typed_mem >>
      impl_tac >- asm_rewrite_tac[] >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `t1`, `ann`, `bl`, `el`,
               `tys`, `v1`, `v2`, `es0`, `tenv`, `tv1`]
    mp_tac binop_frag_compare_typed_mem >>
  impl_tac >- (asm_rewrite_tac[] >> Cases_on `bop` >> fs[]) >> simp[]
QED

(* From exprSimBinopFrag. *)
Theorem binop_frag_word_typed_mem:
  !ctx func cenv cx bop ann t1 t2 bl el tys v1 v2 es0 tenv tv1 tv2.
    well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
    (bop = Exp ==>
      (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
      (!n. bl = SOME n ==> v1 = IntV n) /\
      (!n. el = SOME n ==> v2 = IntV n)) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    word_value_type t1 /\ word_value_type t2 /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop t1 ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bop = ExpMod` >- gvs[well_typed_binop_def] >>
  Cases_on `bop = Exp`
  >- binop_dispatch_mem_tac binop_frag_pow_mem >>
  Cases_on `MEM bop [Add; Sub; Mul; Div; Mod]`
  >- binop_dispatch_mem_tac binop_frag_arith_any_mem >>
  Cases_on `MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]`
  >- binop_dispatch_mem_tac binop_frag_unsafe_any_mem >>
  Cases_on `bop = ShL \/ bop = ShR`
  >- binop_dispatch_mem_tac binop_frag_shift_any_mem >>
  Cases_on `bop = In \/ bop = NotIn`
  >- binop_dispatch_mem_tac binop_frag_in_any_mem >>
  binop_dispatch_mem_tac binop_frag_rest_any_mem
QED

(* From exprSimBinopFrag. *)
Theorem binop_frag_typed_mem:
  !ctx func cenv cx bop ann e1 e2 v1 v2 es0 tv1 tv2.
    well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
    (bop = Exp ==>
      IS_SOME (expr_int_literal e1) \/
      ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
    (!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
    (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n) /\
    (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
    type_bits (expr_type e1) MOD 8 = 0 /\
    word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
    evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
    value_has_type tv1 v1 /\
    evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
    value_has_type tv2 v2 ==>
    binop_frag_val_mem ctx func cenv cx bop (expr_type e1) ann
      (if bop = Exp then expr_int_literal e1 else NONE)
      (if bop = Exp then expr_int_literal e2 else NONE)
      [expr_type e1; expr_type e2] v1 v2 es0
Proof
  rpt strip_tac >>
  irule binop_frag_word_typed_mem >>
  Cases_on `bop = Exp` >> gvs[] >> metis_tac[]
QED
