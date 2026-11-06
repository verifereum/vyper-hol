(* Concrete semantic suffix runs, before pointer-path packaging. *)
Theory bodyPtrBopScalarRun
Ancestors exprSimArith exprSimBinopFrag exprBopSimDefs exprLowering
  freshWrites compileEnv valueEncoding vyperInterpreter loweringSlice
  vyperContext vyperValueOperation varsExt appendStorageStageTransportPtr
  fragGasFresh list arithmeticProps builtinProps exprBopBitwise exprSimCompare exprBopShift vyperAST
  vyperTypeSystem

Theorem bop_checked_fresh_run:
  MEM bop [Add; Sub; Mul] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qabbrev_tac `rr = if bop = Add then i1 + i2 else
                      if bop = Sub then i1 - i2 else i1 * i2` >>
  `bop_result cx ann bop tys (IntV i1) (IntV i2) es =
    if within_int_bound u rr then INL (IntV rr)
    else INR (Error (RuntimeError "bounded_int_op bound"))` by
    (Cases_on `bop` >>
     gvs[Abbr `rr`, bop_result_def, evaluate_builtin_def,
         evaluate_binop_def, bounded_int_op_def] >> rw[]) >>
  asm_rewrite_tac[] >>
  `((within_int_bound u rr ==> ?t.
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (i2w rr)) /\
    (~within_int_bound u rr ==> ?t.
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t))` by
    (gvs[Abbr `rr`, compile_binop_def]
     >- (drule_all compile_safe_add_run >> simp[])
     >- (drule_all compile_safe_sub_run >> simp[]) >>
     drule_all compile_safe_mul_run >> simp[]) >>
  Cases_on `within_int_bound u rr` >>
  gvs[word_value_def, val_to_w256_def] >> metis_tac[]
QED

Theorem bop_run_drop_fresh_transport:
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~is_ext_call_op i.inst_opcode) code /\
  ((?v t. res = INL v /\ word_value v /\
      run_inst_seq code (drop_fresh sa s) = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
   (?m t. res = INR (Error (RuntimeError m)) /\
      run_inst_seq code (drop_fresh sa s) = Abort Revert_abort t)) ==>
  (?v t. res = INL v /\ word_value v /\
      run_inst_seq code s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. res = INR (Error (RuntimeError m)) /\
      run_inst_seq code s = Abort Revert_abort t)
Proof
  strip_tac >>
  `vars_ext_result (run_inst_seq code (drop_fresh sa s))
                   (run_inst_seq code s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >> metis_tac[vars_ext_eval_operand]
QED

Theorem bop_checked_run:
  MEM bop [Add; Sub; Mul] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        (gvs[compile_binop_def] >> simp[straight_fresh_checked]) >>
      `writes_fresh sa (emitted_insts sa sb)` by
        metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> irule bop_checked_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at Any) >> gvs[eval_operand_drop_fresh]
QED

Theorem bop_divmod_fresh_run:
  MEM bop [Div; Mod] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_assum `type_to_int_bound ty = _` (strip_assume_tac o MATCH_MP type_to_int_bound_bits) >>
  `math_val ty (i2w i1 : bytes32) = i1 /\
   math_val ty (i2w i2 : bytes32) = i2` by gvs[math_val_i2w] >>
  `i2 = 0 <=> i2w i2 = (0w : bytes32)` by
    (eq_tac >- (strip_tac >> simp[integer_wordTheory.i2w_0]) >>
     metis_tac[i2w_eq_0_within]) >>
  `((i2 = 0 \/ (bop = Div /\ is_signed_type ty /\
                 i1 = -&(2 ** (type_bits ty - 1)) /\ i2 = -1)) ==>
     ?m. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
           INR (Error (RuntimeError m))) /\
   (~(i2 = 0 \/ (bop = Div /\ is_signed_type ty /\
                  i1 = -&(2 ** (type_bits ty - 1)) /\ i2 = -1)) ==>
     ?z. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL (IntV z) /\
       (i2w z : bytes32) =
         (if bop = Div then (if is_signed_type ty then safe_sdiv else safe_div)
          else (if is_signed_type ty then safe_smod else safe_mod))
           (i2w i1) (i2w i2))` by
    (irule bop_result_divmod >> simp[] >> metis_tac[]) >>
  qpat_assum `~_ ==> ?z. _` mp_tac >>
  qmatch_goalsub_abbrev_tac `~BAD ==> _` >> strip_tac >>
  Cases_on `BAD`
  >- (qpat_x_assum `~BAD ==> _` kall_tac >>
      qpat_x_assum `_ ==> ?m. _` mp_tac >> simp[] >> strip_tac >>
      disj2_tac >> qexists_tac `m` >> simp[] >>
      gvs[markerTheory.Abbrev_def, compile_binop_def]
      >- metis_tac[compile_safe_div_by_zero]
      >- (gvs[math_val_def] >> irule compile_safe_div_overflow >>
          simp[] >> metis_tac[]) >>
      metis_tac[compile_safe_mod_by_zero]) >>
  qpat_x_assum `~BAD ==> _` mp_tac >> simp[] >> strip_tac >>
  disj1_tac >> qexists_tac `IntV z` >>
  simp[word_value_def, val_to_w256_def] >>
  `in_type_range ty i1` by gvs[in_type_range_within] >>
  gvs[markerTheory.Abbrev_def, compile_binop_def]
  >- (drule_at (Pat `compile_safe_div _ _ _ _ = _`) compile_safe_div_ok >>
      Cases_on `is_signed_type ty` >> gvs[math_val_def]) >>
  drule_all compile_safe_mod_correct >> Cases_on `is_signed_type ty` >> simp[]
QED

Theorem bop_divmod_run:
  MEM bop [Div; Mod] /\
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_assum `type_to_int_bound ty = _` (strip_assume_tac o MATCH_MP type_to_int_bound_bits) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        (gvs[compile_binop_def] >> simp[straight_fresh_checked]) >>
      `writes_fresh sa (emitted_insts sa sb)` by
        metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> irule bop_divmod_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at Any) >> gvs[eval_operand_drop_fresh]
QED

Theorem bop_unsafe_run:
  MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
  type_to_int_bound ann =
    SOME (if is_signed_type ty then Signed (type_bits ty)
          else Unsigned (type_bits ty)) /\
  0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
  within_int_bound (if is_signed_type ty then Signed (type_bits ty)
                   else Unsigned (type_bits ty)) i2 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  eval_operand x s = SOME (i2w i1) /\
  eval_operand y s = SOME (i2w i2) ==>
  ?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `?v. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
       word_value v /\ val_to_w256 v =
         truncate_to_bits (type_bits ty) (is_signed_type ty)
           (unsafe_word_op bop ty (i2w i1) (i2w i2))` by
    (simp[GSYM val_to_w256_def] >> irule bop_result_unsafe >> simp[]) >>
  qexists_tac `v` >> simp[] >>
  qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_binop_unsafe] >> strip_tac >>
  irule compile_unsafe_binop_correct >>
  goal_assum (drule_at (Pat `compile_unsafe_binop`)) >>
  simp[] >> rpt strip_tac >> irule step_unsafe_opcode >> simp[]
QED

Theorem bop_power_fresh_run:
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
  (!n. bl = SOME n ==> i1 = n) /\ (!n. el = SOME n ==> i2 = n) /\
  compile_binop Exp x y ty bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w i1) /\ eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann Exp tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann Exp tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  qpat_assum `type_to_int_bound ty = _`
    (strip_assume_tac o MATCH_MP type_to_int_bound_bits) >>
  `compile_safe_pow x y ty bl el sa = (op,sb)` by gvs[compile_binop_def] >>
  `((0 <= i2 /\ within_int_bound u (i1 ** Num i2) ==> ?t.
       run_inst_seq (emitted_insts sa sb) s = OK t /\
       eval_operand op t = SOME (i2w (i1 ** Num i2))) /\
    (~(0 <= i2 /\ within_int_bound u (i1 ** Num i2)) ==> ?t.
       run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t))` by
    (drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >>
     disch_then (qspecl_then [`i1`, `i2`, `s`] mp_tac) >> gvs[] >> metis_tac[]) >>
  qpat_assum `type_to_int_bound ann = _`
    (assume_tac o MATCH_MP bop_result_power) >>
  asm_rewrite_tac[] >> Cases_on `i2 < 0`
  >- (gvs[] >> metis_tac[integerTheory.INT_NOT_LE]) >>
  Cases_on `within_int_bound u (i1 ** Num i2)` >>
  gvs[word_value_def, val_to_w256_def] >> metis_tac[integerTheory.INT_NOT_LE]
QED

Theorem bop_power_run:
  type_to_int_bound ty = SOME u /\ type_to_int_bound ann = SOME u /\
  0 < type_bits ty /\ type_bits ty <= 256 /\ type_bits ty MOD 8 = 0 /\
  within_int_bound u i1 /\ within_int_bound u i2 /\
  (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
  (!n. bl = SOME n ==> i1 = n) /\ (!n. el = SOME n ==> i2 = n) /\
  compile_binop Exp x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (i2w i1) /\ eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann Exp tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann Exp tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop Exp x y ty bl el)` by
        simp[compile_binop_def, straight_fresh_compile_safe_pow] >>
      `writes_fresh sa (emitted_insts sa sb)` by
        metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> irule bop_power_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at Any) >> gvs[eval_operand_drop_fresh]
QED

Theorem bop_bitwise_fresh_run:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
    within_int_bound
      (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
    within_int_bound
      (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fresh_vars_wrt sa s /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  ?v t. bop_result cx ann bop tys v1 v2 es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_result_bitwise >> strip_tac >>
  qexists_tac `v` >> simp[] >> drule_all compile_bitwise_run >> simp[]
QED

Theorem bop_bitwise_run:
  (bop = And \/ bop = Or \/ bop = XOr) /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  (!i1 i2. v1 = IntV i1 /\ v2 = IntV i2 ==>
    within_int_bound
      (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i1 /\
    within_int_bound
      (case type_to_int_bound ann of SOME u => u | NONE => Unsigned 0) i2) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        metis_tac[straight_fresh_compile_bitwise] >>
      `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> disj1_tac >> irule bop_bitwise_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at Any) >> gvs[eval_operand_drop_fresh]
QED

Theorem bop_compare_words_fresh_run:
  MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
  res = INL (BoolV (eval_compare bop ty w1 w2)) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fresh_vars_wrt sa s /\
  eval_operand x s = SOME w1 /\ eval_operand y s = SOME w2 ==>
  ?v t. res = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `compile_compare bop x y ty sa = (op,sb)` by
    (gvs[compile_binop_def]) >>
  drule_all compile_compare_correct >> strip_tac >>
  qexists_tac `BoolV (eval_compare bop ty w1 w2)` >>
  Cases_on `eval_compare bop ty w1 w2` >>
  gvs[word_value_def, val_to_w256_def, venomExecSemanticsTheory.bool_to_word_def] >> metis_tac[]
QED

Theorem bop_compare_words_run:
  MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
  res = INL (BoolV (eval_compare bop ty w1 w2)) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME w1 /\ eval_operand y s = SOME w2 ==>
  (?v t. res = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. res = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        metis_tac[straight_fresh_compare] >>
      `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> disj1_tac >> irule bop_compare_words_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at Any) >> gvs[eval_operand_drop_fresh]
QED

Theorem bop_compare_run:
  MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE] /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
  (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
  (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_compare_words_run >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> gvs[] >>
  irule bop_result_compare >> simp[] >> qexists_tac `tv` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem bop_compare_bytes_run:
  (bop = Eq \/ bop = NotEq) /\
  (tv = BaseTV AddressT \/ ?m. tv = BaseTV (BytesT (Fixed m)) /\ m <= 32) /\
  value_has_type tv (BytesV b1) /\ value_has_type tv (BytesV b2) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (typed_val_to_w256 tv (BytesV b1)) /\
  eval_operand y s = SOME (typed_val_to_w256 tv (BytesV b2)) ==>
  (?v t. bop_result cx ann bop tys (BytesV b1) (BytesV b2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (BytesV b1) (BytesV b2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(typed_val_to_w256 tv (BytesV b1) = typed_val_to_w256 tv (BytesV b2)
       <=> b1 = b2)` by
    (irule typed_val_to_w256_bytes_11 >> simp[]) >>
  irule bop_compare_words_run >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> gvs[] >>
  gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
      binop_negate_def, eval_compare_def]
QED

Theorem bop_minmax_fresh_run:
  (bop = Min \/ bop = Max) /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
  (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
  (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fresh_vars_wrt sa s /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  ?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all bop_result_minmax >> strip_tac >>
  qexists_tac `v` >> simp[] >> drule_all compile_minmax_correct >> simp[]
QED

Theorem bop_minmax_run:
  (bop = Min \/ bop = Max) /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  word_value v1 /\ value_has_type tv v1 /\ value_has_type tv v2 /\
  (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
  (!m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        metis_tac[straight_fresh_minmax] >>
      `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> disj1_tac >> irule bop_minmax_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  gvs[eval_operand_drop_fresh] >> qexists_tac `tv` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem bop_shift_fresh_run:
  (bop = ShL \/ bop = ShR) /\ (bop = ShL ==> n = 256) /\
  0 < n /\ n <= 256 /\ within_int_bound (Unsigned 256) i2 /\
  type_to_int_bound ann =
    SOME (if is_signed_type ty then Signed n else Unsigned n) /\
  within_int_bound (if is_signed_type ty then Signed n else Unsigned n) i1 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w i1) /\ eval_operand y s = SOME (i2w i2) ==>
  ?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?v. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
       word_value v /\ val_to_w256 v =
         if bop = ShL then word_lsl (val_to_w256 (IntV i1)) (w2n (val_to_w256 (IntV i2)))
         else if is_signed_type ty then word_asr (val_to_w256 (IntV i1)) (w2n (val_to_w256 (IntV i2)))
         else word_lsr (val_to_w256 (IntV i1)) (w2n (val_to_w256 (IntV i2)))` by
    (Cases_on `bop = ShL`
     >- (`n = 256` by metis_tac[] >> irule bop_result_shift >> gvs[]) >>
     `bop = ShR` by metis_tac[] >> asm_rewrite_tac[] >>
     irule bop_result_shr >> simp[] >> qexists_tac `n` >> simp[]) >>
  qexists_tac `v` >> simp[val_to_w256_def] >> drule_all compile_shift_run >> simp[]
QED

Theorem bop_shift_run:
  (bop = ShL \/ bop = ShR) /\ (bop = ShL ==> n = 256) /\
  0 < n /\ n <= 256 /\ within_int_bound (Unsigned 256) i2 /\
  type_to_int_bound ann =
    SOME (if is_signed_type ty then Signed n else Unsigned n) /\
  within_int_bound (if is_signed_type ty then Signed n else Unsigned n) i1 /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (i2w i1) /\ eval_operand y s = SOME (i2w i2) ==>
  (?v t. bop_result cx ann bop tys (IntV i1) (IntV i2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (IntV i1) (IntV i2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y ty bl el)` by
        metis_tac[straight_fresh_compile_shift] >>
      `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >> disj1_tac >> irule bop_shift_fresh_run >>
  simp[fresh_vars_wrt_drop_fresh] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[eval_operand_drop_fresh] >> qexists_tac `n` >> simp[] >> metis_tac[]
QED

Theorem bop_decimal_mul_fresh_run:
  within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 /\
  compile_binop Mul x y (BaseT DecimalT) bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w d1) /\ eval_operand y s = SOME (i2w d2) ==>
  (?v t. bop_result cx ann Mul tys (DecimalV d1) (DecimalV d2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann Mul tys (DecimalV d1) (DecimalV d2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  `in_type_range (BaseT DecimalT) d1 /\ in_type_range (BaseT DecimalT) d2`
    by simp[in_type_range_decimal] >>
  gvs[compile_binop_def] >>
  drule_all compile_safe_decimal_mul_run >>
  simp[in_type_range_decimal] >> strip_tac >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       decimal_sgn_quot, bounded_decimal_op_def] >>
  Cases_on `within_int_bound (Signed 168) (d1 * d2 quot 10000000000)` >>
  gvs[word_value_def, val_to_w256_def] >> metis_tac[]
QED

Theorem bop_decimal_div_fresh_run:
  within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 /\
  compile_binop Div x y (BaseT DecimalT) bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w d1) /\ eval_operand y s = SOME (i2w d2) ==>
  (?v t. bop_result cx ann Div tys (DecimalV d1) (DecimalV d2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann Div tys (DecimalV d1) (DecimalV d2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  `w2i (i2w d1 : bytes32) = d1 /\ w2i (i2w d2 : bytes32) = d2` by
    (conj_tac >> irule integer_wordTheory.w2i_i2w >>
     fs[vyperValueTheory.within_int_bound_def, wordsTheory.INT_MIN_def,
        wordsTheory.INT_MAX_def, wordsTheory.dimword_def] >> intLib.ARITH_TAC) >>
  `(i2w d1 * n2w 10000000000 : bytes32) = i2w (d1 * 10000000000)` by
    (qspecl_then [`i2w d1 : bytes32`, `n2w 10000000000 : bytes32`] mp_tac
       integer_wordTheory.word_mul_i2w >>
     asm_rewrite_tac[w2i_decimal_divisor] >>
     disch_then (SUBST1_TAC o SYM) >> REFL_TAC) >>
  `(i2w d2 = (0w : bytes32)) <=> d2 = 0` by
    (eq_tac >> strip_tac >> simp[integer_wordTheory.i2w_0] >>
     qpat_x_assum `w2i (i2w d2) = d2` (SUBST1_TAC o SYM) >>
     asm_simp_tac std_ss [integer_wordTheory.word_0_w2i]) >>
  gvs[compile_binop_def, is_decimal_type_def, decimal_divisor_def] >>
  drule_all compile_safe_decimal_div_run >> strip_tac >>
  simp[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
       bounded_decimal_op_def] >>
  Cases_on `d2 = 0` >- (gvs[] >> metis_tac[]) >>
  `safe_sdiv (i2w d1 * n2w 10000000000) (i2w d2) =
     (i2w (d1 * 10000000000) / i2w d2 : bytes32)` by
    asm_simp_tac std_ss [venomExecSemanticsTheory.safe_sdiv_def] >>
  Cases_on `within_int_bound (Signed 168)
              (w2i (i2w (d1 * 10000000000) / i2w d2 : bytes32))` >>
  gvs[word_value_def, val_to_w256_def, in_type_range_decimal,
      integer_wordTheory.i2w_w2i] >> metis_tac[]
QED

Theorem bop_decimal_run_transfer:
  ((?v t. ri = INL v /\ word_value v /\ run_inst_seq code s = OK t /\
     eval_operand op t = SOME (val_to_w256 v)) \/
   (?m t. ri = INR (Error (RuntimeError m)) /\
     run_inst_seq code s = Abort Revert_abort t)) /\
  ((?z. ri = INL (IntV z) /\ rd = INL (DecimalV z)) \/
   (?m m'. ri = INR (Error (RuntimeError m)) /\
     rd = INR (Error (RuntimeError m')))) ==>
  (?v t. rd = INL v /\ word_value v /\ run_inst_seq code s = OK t /\
     eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. rd = INR (Error (RuntimeError m)) /\
     run_inst_seq code s = Abort Revert_abort t)
Proof
  strip_tac >> gvs[word_value_def, val_to_w256_def] >> metis_tac[]
QED

Theorem bop_decimal_add_sub_mod_fresh_run:
  MEM bop [Add; Sub; Mod] /\
  within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 /\
  compile_binop bop x y (BaseT DecimalT) bl el sa = (op,sb) /\
  fresh_vars_wrt sa s /\
  eval_operand x s = SOME (i2w d1) /\ eval_operand y s = SOME (i2w d2) ==>
  (?v t. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_binop bop x y (BaseT (IntT 168)) bl el sa = (op,sb)` by
    (qpat_x_assum `compile_binop _ _ _ _ _ _ _ = _` mp_tac >>
     gvs[compile_binop_def, compile_safe_add_def, compile_safe_sub_def,
         compile_safe_mod_def, clamp_and_return_def, compile_clamp_def,
         type_bounds_def, type_bits_def, is_signed_type_def]) >>
  irule bop_decimal_run_transfer >>
  qexists_tac `bop_result cx (BaseT (IntT 168)) bop tys (IntV d1) (IntV d2) es` >>
  conj_tac
  >- (gvs[bop_result_def, evaluate_builtin_def, evaluate_binop_def,
          bounded_int_op_def, bounded_decimal_op_def, type_to_int_bound_def,
          int_bound_bits_def] >> rw[]) >>
  Cases_on `bop = Mod`
  >- (gvs[] >> irule bop_divmod_fresh_run >>
      simp[type_to_int_bound_def, type_bits_def] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      simp[type_to_int_bound_def, type_bits_def]) >>
  irule bop_checked_fresh_run >> simp[type_to_int_bound_def, type_bits_def] >>
  conj_tac >- (gvs[] >> metis_tac[]) >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  gvs[type_to_int_bound_def, type_bits_def]
QED

Theorem bop_decimal_arith_run:
  MEM bop [Add; Sub; Mul; Div; Mod] /\
  within_int_bound (Signed 168) d1 /\ within_int_bound (Signed 168) d2 /\
  compile_binop bop x y (BaseT DecimalT) bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (i2w d1) /\ eval_operand y s = SOME (i2w d2) ==>
  (?v t. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys (DecimalV d1) (DecimalV d2) es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_run_drop_fresh_transport >> conj_tac
  >- (`straight_fresh (compile_binop bop x y (BaseT DecimalT) bl el)` by
        (gvs[compile_binop_def, is_decimal_type_def, decimal_divisor_def] >>
         simp[straight_fresh_checked, straight_fresh_decimal_div]) >>
      `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
      drule writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
  qexists_tac `sa` >>
  `eval_operand x (drop_fresh sa s) = SOME (i2w d1) /\
   eval_operand y (drop_fresh sa s) = SOME (i2w d2)` by
    simp[eval_operand_drop_fresh] >>
  Cases_on `bop = Mul`
  >- (gvs[] >> irule bop_decimal_mul_fresh_run >>
      simp[fresh_vars_wrt_drop_fresh] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  Cases_on `bop = Div`
  >- (gvs[] >> irule bop_decimal_div_fresh_run >>
      simp[fresh_vars_wrt_drop_fresh] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  irule bop_decimal_add_sub_mod_fresh_run >> simp[fresh_vars_wrt_drop_fresh] >>
  conj_tac >- (gvs[] >> metis_tac[]) >> gvs[] >> metis_tac[]
QED

Theorem bop_arith_typed_run:
  MEM bop [Add; Sub; Mul; Div; Mod] /\ well_typed_binop ann bop t1 t2 /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  compile_binop bop x y t1 bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_numeric_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  Cases_on `ann = BaseT DecimalT`
  >- (gvs[] >>
      qspecl_then [`tenv`, `tv1`, `v1`] mp_tac decimal_type_value >>
      qspecl_then [`tenv`, `tv1`, `v2`] mp_tac decimal_type_value >>
      asm_rewrite_tac[] >> rpt strip_tac >> gvs[val_to_w256_def] >>
      irule bop_decimal_arith_run >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  `is_int_type ann` by gvs[] >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> gnvs[val_to_w256_def] >>
  Cases_on `MEM bop [Div; Mod]`
  >- (irule bop_divmod_run >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  irule bop_checked_run >> simp[] >>
  conj_tac >- (Cases_on `bop` >> gvs[]) >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Theorem bop_unsafe_typed_run:
  MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv] /\
  well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  compile_binop bop x y t1 bl el sa = (op,sb) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  ?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)
Proof
  strip_tac >>
  `t1 = ann /\ t2 = ann /\ is_int_type ann` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> gnvs[val_to_w256_def] >>
  irule bop_unsafe_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Theorem bop_power_typed_run:
  well_typed_binop ann Exp t1 t2 /\
  (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
  (!n. bl = SOME n ==> v1 = IntV n) /\
  (!n. el = SOME n ==> v2 = IntV n) /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  compile_binop Exp x y t1 bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann Exp tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann Exp tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `t1 = ann /\ t2 = ann /\ is_int_type ann` by gvs[well_typed_binop_def] >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qpat_x_assum `t2 = ann` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> gnvs[val_to_w256_def] >>
  `type_bits ann MOD 8 = 0` by metis_tac[int_type_byte_width] >>
  irule bop_power_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]
QED

Theorem bop_compare_typed_run:
  MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\ word_value_type ty /\
  evaluate_type tenv ty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  `word_value v1 /\ (is_uint256 ty <=> tv = BaseTV (UintT 256)) /\
   !m. tv = BaseTV (UintT m) \/ tv = BaseTV (IntT m) \/ tv = FlagTV m ==>
       m <= 256` by
    (qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac word_value_type_value_cases >>
     asm_rewrite_tac[] >> rpt strip_tac >>
     gvs[word_value_def, is_uint256_def]) >>
  Cases_on `bop = Min \/ bop = Max`
  >- (irule bop_minmax_run >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      simp[] >> qexists_tac `tv` >> simp[] >> first_assum ACCEPT_TAC) >>
  irule bop_compare_run >> simp[] >>
  conj_tac >- (Cases_on `bop` >> gvs[]) >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `tv` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem bop_bitwise_typed_run:
  (bop = And \/ bop = Or \/ bop = XOr) /\ word_value_type ty /\
  evaluate_type tenv ty = SOME tv /\
  value_has_type tv v1 /\ value_has_type tv v2 /\
  expr_res_ok (bop_result cx ty bop tys v1 v2 es) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ty bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ty bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_bitwise_run >> simp[] >> reverse conj_tac
  >- (goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]) >>
  qspecl_then [`tenv`, `ty`, `tv`, `v1`] mp_tac word_value_type_value_cases >>
  qspecl_then [`tenv`, `ty`, `tv`, `v2`] mp_tac word_value_type_value_cases >>
  asm_rewrite_tac[] >> rpt strip_tac >> gvs[type_to_int_bound_def]
QED

Theorem bop_shift_typed_run:
  (bop = ShL \/ bop = ShR) /\ well_typed_binop ann bop t1 t2 /\
  (?i. v2 = IntV i /\ 0 <= i) /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  compile_binop bop x y t1 bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  `t1 = ann /\ is_int_type ann /\ is_int_type t2 /\
   (bop = ShL ==> type_bits ann = 256)` by
    (Cases_on `bop` >> gvs[well_typed_binop_def, type_bits_def]) >>
  qpat_x_assum `t1 = ann` SUBST_ALL_TAC >>
  qspecl_then [`tenv`, `ann`, `tv1`, `v1`] mp_tac int_type_value >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  asm_rewrite_tac[] >> rpt strip_tac >> gnvs[val_to_w256_def] >>
  `within_int_bound (Unsigned 256) i` by
    (Cases_on `is_signed_type t2` >> fs[] >>
     metis_tac[within_int_bound_unsigned_256]) >>
  irule bop_shift_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[] >> qexists_tac `type_bits ann` >> simp[]
QED

Theorem bop_rest_typed_run:
  MEM bop [And; Or; XOr; Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max] /\
  well_typed_binop ann bop t1 t2 /\ word_value_type t1 /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  compile_binop bop x y t1 bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  strip_tac >>
  `t2 = t1` by
    (qpat_x_assum `MEM _ _` mp_tac >> rw[] >> gvs[well_typed_binop_def]) >>
  qpat_x_assum `t2 = t1` SUBST_ALL_TAC >>
  `tv2 = tv1` by gvs[] >> pop_assum SUBST_ALL_TAC >>
  Cases_on `bop = And \/ bop = Or \/ bop = XOr`
  >- (`ann = t1` by
        (qpat_x_assum `bop = _ \/ _` strip_assume_tac >>
         gvs[well_typed_binop_def]) >>
      pop_assum SUBST_ALL_TAC >> irule bop_bitwise_typed_run >> simp[] >>
      conj_tac
      >- (goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >> simp[]) >>
      metis_tac[]) >>
  `MEM bop [Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max]` by
    (Cases_on `bop` >> gvs[]) >>
  irule bop_compare_typed_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem bop_word_typed_run:
  bop <> In /\ bop <> NotIn /\
  well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
  (bop = Exp ==> (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n)) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  word_value_type t1 /\ word_value_type t2 /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
  compile_binop bop x y t1 bl el sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\ word_value v /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop tys v1 v2 es = INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bop = ExpMod` >- gvs[well_typed_binop_def] >>
  Cases_on `bop = Exp`
  >- (gvs[] >> irule bop_power_typed_run >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  Cases_on `MEM bop [Add; Sub; Mul; Div; Mod]`
  >- (irule bop_arith_typed_run >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  Cases_on `MEM bop [UnsafeAdd; UnsafeSub; UnsafeMul; UnsafeDiv]`
  >- (disj1_tac >> irule bop_unsafe_typed_run >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  Cases_on `bop = ShL \/ bop = ShR`
  >- (`?i. v2 = IntV i /\ 0 <= i` by metis_tac[] >>
      irule bop_shift_typed_run >> simp[] >>
      goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  `MEM bop [And; Or; XOr; Lt; Gt; Eq; NotEq; LtE; GtE; Min; Max]` by
    (Cases_on `bop` >> gvs[]) >>
  irule bop_rest_typed_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Theorem bop_scalar_typed_run:
  bop <> In /\ bop <> NotIn /\
  well_typed_binop ann bop (expr_type e1) (expr_type e2) /\
  (bop = Exp ==> IS_SOME (expr_int_literal e1) \/
    ?n. expr_int_literal e2 = SOME n /\ 0 <= n) /\
  (!n. expr_int_literal e1 = SOME n ==> v1 = IntV n) /\
  (!n. expr_int_literal e2 = SOME n ==> v2 = IntV n) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  type_bits (expr_type e1) MOD 8 = 0 /\
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
  value_has_type tv1 v1 /\
  evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
  value_has_type tv2 v2 /\
  expr_res_ok (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) sa = (op,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) ==>
  (?v t. bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es = INL v /\
    word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (val_to_w256 v)) \/
  (?m t. bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 es =
      INR (Error (RuntimeError m)) /\
    run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule bop_word_typed_run >> simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED
