(* Counted binary operator producer and its source facts. *)
Theory exprBopShift
Ancestors
  exprBopSimDefs exprBopSimProps exprSimBopTyped exprBopStraight
  exprSimProps
  exprSimDefs
  loweringPosts
  list rich_list finite_map pred_set
  fragExec varsExt  freshWrites exprBopLowering loweringSlice
  localPtrsProps vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes
  exprLowering emitHelper emitHelperProps exprLoweringProps compileEnv
  vyperInterpreter vyperState vyperValueOperation vyperContext
  valueEncoding venomExecSemantics venomInst venomState
  vyperValue integer integer_word int_bitwise words intBits vyperTyping
Libs
  pairLib

Theorem bop_result_shift:
  !cx ann bop ty v1 v2 es i1 i2.
    (bop = ShL \/ bop = ShR) /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    within_int_bound (Unsigned 256) i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed 256 else Unsigned 256) /\
    within_int_bound (if is_signed_type ty then Signed 256 else Unsigned 256)
      i1 ==>
    ?v. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
        val_to_w256 v =
          if bop = ShL then word_lsl (val_to_w256 v1) (w2n (val_to_w256 v2))
          else if is_signed_type ty
          then word_asr (val_to_w256 v1) (w2n (val_to_w256 v2))
          else word_lsr (val_to_w256 v1) (w2n (val_to_w256 v2))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `~(i2 < 0) /\ w2n (i2w i2 : bytes32) = Num i2` by
    (fs[within_int_bound_def] >>
     `?k. i2 = &k` by metis_tac[NUM_POSINT_EXISTS] >>
     gvs[i2w_pos, w2n_n2w, dimword_def]) >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      val_to_w256_def, word_value_def] >>
  Cases_on `is_signed_type ty` >> gvs[] >>
  FIRST [
    (* ShL, signed: wrapped by signed_int_mod *)
    simp[val_to_w256_def] >>
    qmatch_goalsub_abbrev_tac `signed_int_mod 256 rr` >>
    `signed_int_mod 256 rr = w2i (i2w rr : bytes32)` by
      (qspec_then `rr` mp_tac
         (INST_TYPE [alpha |-> ``:256``] signed_int_mod_w2i) >> simp[]) >>
    simp[i2w_w2i, Abbr `rr`, i2w_int_shift_left] >> NO_TAC,
    (* ShL, unsigned: wrapped by int_mod *)
    simp[val_to_w256_def] >>
    qmatch_goalsub_abbrev_tac `i2w (rr % _)` >>
    `rr % &dimword (:256) = &w2n (i2w rr : bytes32)` by simp[w2n_i2w] >>
    fs[dimword_def, i2w_w2n, Abbr `rr`, i2w_int_shift_left] >> NO_TAC,
    irule i2w_int_shift_right_signed >> simp[] >> NO_TAC,
    irule i2w_int_shift_right_unsigned >> simp[]]
QED

Theorem straight_fresh_compile_shift:
  !bop x y ty bl el. (bop = ShL \/ bop = ShR) ==>
    straight_fresh (compile_binop bop x y ty bl el)
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_binop_def] >>
  Cases_on `is_signed_type ty` >> simp[] >>
  irule straight_fresh_emit_op >> simp[fresh_write_op_def]
QED

Theorem compile_shift_run:
  !bop x y ty bl el sa sb op ss w1 w2.
    (bop = ShL \/ bop = ShR) /\
    compile_binop bop x y ty bl el sa = (op,sb) /\
    fresh_vars_wrt sa ss /\ eval_operand x ss = SOME w1 /\
    eval_operand y ss = SOME w2 ==>
    ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
      eval_operand op ss' = SOME
        (if bop = ShL then word_lsl w1 (w2n w2)
         else if is_signed_type ty then word_asr w1 (w2n w2)
         else word_lsr w1 (w2n w2))
Proof
  rpt gen_tac >> strip_tac >> gvs[compile_binop_def]
  >- (qspecl_then [`SHL`, `\a b. word_lsl b (w2n a)`]
        (drule_at (Pat `emit_op _ _ _ = _`) o BETA_RULE)
        emit_op_pure2_correct >>
      disch_then (qspecl_then [`w2`, `w1`, `ss`] mp_tac) >>
      simp[step_SHL] >> metis_tac[]) >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- (qspecl_then [`SAR`, `\a b. word_asr b (w2n a)`]
        (drule_at (Pat `emit_op _ _ _ = _`) o BETA_RULE)
        emit_op_pure2_correct >>
      disch_then (qspecl_then [`w2`, `w1`, `ss`] mp_tac) >>
      simp[step_SAR] >> metis_tac[]) >>
  drule_all emit_op_SHR_correct >> metis_tac[]
QED

(* binop_frag for ShL and ShR of a 256-bit integer by a uint256 amount:
   one instruction. *)
Theorem compile_shift_sim:
  !ctx func cenv cx bop ty ann bl el v1 v2 es0 i1 i2.
    (bop = ShL \/ bop = ShR) /\ v1 = IntV i1 /\ v2 = IntV i2 /\
    within_int_bound (Unsigned 256) i2 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed 256 else Unsigned 256) /\
    within_int_bound (if is_signed_type ty then Signed 256 else Unsigned 256)
      i1 ==>
    binop_frag ctx func cenv cx bop ty ann bl el tys v1 v2 es0
Proof
  rpt gen_tac >> strip_tac >>
  irule binop_frag_straight >>
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

(* Retained legacy proof:
Proof
  rpt gen_tac >> strip_tac >> simp[binop_frag_def, binop_frag_words_def] >> rpt gen_tac >>
  strip_tac >>
  qspecl_then [`cx`, `ann`, `bop`, `ty`, `v1`, `v2`, `es0`, `i1`, `i2`]
    mp_tac bop_result_shift >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  irule frag_exec_pointwise >> rpt strip_tac >> gvs[compile_binop_def] >>
  qpat_x_assum `_ sa = (op, sb)` mp_tac >> rw[] >>
  drule emit_op_frag >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es0`, `s0`,
                           `val_to_w256 v`, `\r. F`] mp_tac) >>
  (impl_tac >- simp[step_SHL, step_SHR, step_SAR, is_terminator_def]) >>
  disch_then (fn th => match_mp_tac (MATCH_MP frag_exec_weaken th)) >>
  simp[] >> metis_tac[]
QED

*)

(* Right shift does not narrow its result at the annotation width. *)
Theorem within_int_bound_widen_256:
  !n i. 0 < n /\ n <= 256 ==>
    (within_int_bound (Signed n) i ==> within_int_bound (Signed 256) i) /\
    (within_int_bound (Unsigned n) i ==> within_int_bound (Unsigned 256) i)
Proof
  rpt gen_tac >> strip_tac >>
  `2 ** (n - 1) <= 2 ** (256 - 1)` by
    simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  `2 ** n <= 2 ** 256` by simp[arithmeticTheory.EXP_BASE_LE_MONO] >>
  `0n < 256` by decide_tac >>
  pure_rewrite_tac[within_int_bound_def] >> conj_tac
  >- (strip_tac >> Cases_on `i < 0` >>
      full_simp_tac bool_ss [LET_THM] >>
      qpat_x_assum `if _ then _ else _` mp_tac >>
      pure_asm_rewrite_tac[COND_CLAUSES] >> strip_tac >> decide_tac) >>
  rpt strip_tac >> pure_asm_rewrite_tac[] >> decide_tac
QED

Theorem bop_result_shr:
  !cx ann ty v1 v2 es i1 i2 n.
    v1 = IntV i1 /\ v2 = IntV i2 /\
    within_int_bound (Unsigned 256) i2 /\ 0 < n /\ n <= 256 /\
    type_to_int_bound ann =
      SOME (if is_signed_type ty then Signed n else Unsigned n) /\
    within_int_bound (if is_signed_type ty then Signed n else Unsigned n) i1 ==>
    ?v. bop_result cx ann ShR tys v1 v2 es = INL v /\ word_value v /\
        val_to_w256 v =
          if is_signed_type ty
          then word_asr (val_to_w256 v1) (w2n (val_to_w256 v2))
          else word_lsr (val_to_w256 v1) (w2n (val_to_w256 v2))
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `~(i2 < 0) /\ w2n (i2w i2 : bytes32) = Num i2` by
    (fs[within_int_bound_def] >>
     `?k. i2 = &k` by metis_tac[NUM_POSINT_EXISTS] >>
     gvs[i2w_pos, w2n_n2w, dimword_def]) >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      val_to_w256_def, word_value_def] >>
  Cases_on `is_signed_type ty` >> gvs[]
  >- (irule i2w_int_shift_right_signed >> simp[] >>
      metis_tac[within_int_bound_widen_256]) >>
  irule i2w_int_shift_right_unsigned >> simp[] >>
  metis_tac[within_int_bound_widen_256]
QED

