(* Actual execution of the typed power compiler, including both rejection cases. *)
Theory augAssignFullOperatorPowerExec
Ancestors
  exprSimBinopFrag exprBopLowering exprBopSimDefs freshWrites
  vyperTyping vyperValue vyperTypeSystem exprLowering
  valueEncoding venomExecSemantics loweringSlice
Libs
  intLib

Theorem augassign_power_execution:
  !cx bop ann t1 t2 bl el tys v1 v2 es tenv tv1 tv2 x y sa sb op s.
    bop = Exp /\ well_typed_binop ann bop t1 t2 /\
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n) /\
    evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
    evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
    expr_res_ok (bop_result cx ann bop tys v1 v2 es) /\
    compile_binop bop x y t1 bl el sa = (op,sb) /\
    fresh_vars_wrt sa s /\
    eval_operand x s = SOME (val_to_w256 v1) /\
    eval_operand y s = SOME (val_to_w256 v2) ==>
    (?v t. bop_result cx ann bop tys v1 v2 es = INL v /\
      word_value v /\ run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (val_to_w256 v)) \/
    (?m t. bop_result cx ann bop tys v1 v2 es =
      INR (Error (RuntimeError m)) /\
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t)
Proof
  rpt gen_tac >> strip_tac >>
  `is_int_type t1 /\ is_int_type t2` by gvs[well_typed_binop_def] >>
  qspecl_then [`tenv`, `t1`, `tv1`, `v1`] mp_tac int_type_value >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qspecl_then [`tenv`, `t2`, `tv2`, `v2`] mp_tac int_type_value >>
  (impl_tac >- gvs[]) >> strip_tac >>
  gvs[well_typed_binop_def] >>
  qmatch_asmsub_rename_tac `eval_operand x s = SOME (val_to_w256 (IntV a))` >>
  qmatch_asmsub_rename_tac `eval_operand y s = SOME (val_to_w256 (IntV b))` >>
  `type_bits ann MOD 8 = 0` by metis_tac[int_type_byte_width] >>
  drule_then assume_tac bop_result_power >>
  gvs[compile_binop_def, val_to_w256_def] >>
  (drule_at (Pat `compile_safe_pow _ _ _ _ _ _ = _`) compile_safe_pow_run >>
  disch_then (qspecl_then [`a`, `b`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `b < 0`
  >- (simp[] >> `~(0 <= b)` by intLib.ARITH_TAC >> metis_tac[]) >>
  `0 <= b` by intLib.ARITH_TAC >>
  Cases_on `within_int_bound
    (if is_signed_type ann then Signed (type_bits ann)
     else Unsigned (type_bits ann)) (a ** Num b)` >>
  simp[word_value_def, val_to_w256_def] >> metis_tac[])
QED
