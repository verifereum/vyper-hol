(* Semantic boundaries for the bounded, constructed conditional witness.
   No arbitrary endpoint from expr_sim_ptr is reused here. *)
Theory augAssignPtrConditionalWitness
Ancestors
  augAssignPtrScalarWitnessProbe augAssignPtrScalarJoin
  exprSimConvert exprSimIfExp vyperValueOperation loweringPosts loweringSlice
  vyperInterpreter vyperState vyperAST vyperContext valueEncoding exprLowering compileEnv

Theorem uint256_convert_result:
  within_int_bound (Unsigned 256) i ==>
  convert_result cx (BaseT (UintT 256)) (BaseT (UintT 256)) (IntV i) =
    INL (IntV i)
Proof
  simp[convert_result_def, evaluate_convert_from_def, evaluate_convert_def]
QED

Theorem uint256_convert_forward:
  compile_type_convert op
    (mk_convert_op (BaseT (UintT 256)) (BaseT (UintT 256))) sa = (op,sa)
Proof
  simp[mk_convert_op_def, is_bytestring_type_def, compile_type_convert_def, comp_return_def]
QED

Theorem uint256_convert_post:
  expr_post ctx fn cenv cx e es sa sb s0 ee v op t /\
  expr_type e = BaseT (UintT 256) ==>
  expr_post ctx fn cenv cx
    (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256)) [e])
    es sa sb s0 ee v op t
Proof
  strip_tac >> gvs[expr_post_def, expr_type_def] >> metis_tac[]
QED

Theorem bool_literal_selected_value:
  eval_expr cx (if b then a else c) es = (INL (Value v),ee) ==>
  bind (eval_expr cx
    (IfExp ty (Literal (BaseT BoolT) (BoolL b)) a c)) (read_result cx) es =
    (INL v,ee)
Proof
  Cases_on `b` >>
  simp[Once evaluate_def, Once evaluate_def, switch_BoolV_def, evaluate_literal_def,
       bind_def, return_def, read_result_def, conditional_result_def] >>
  strip_tac >> simp[bind_def, conditional_result_def, return_def, read_result_def]
QED

Theorem uint256_convert_value:
  bind (eval_expr cx e) (read_result cx) es = (INL (IntV i),ee) /\
  expr_type e = BaseT (UintT 256) /\ within_int_bound (Unsigned 256) i ==>
  eval_expr cx
    (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256)) [e]) es =
    (INL (Value (IntV i)),ee)
Proof
  strip_tac >>
  simp[Once evaluate_def, type_builtin_args_length_ok_def, type_check_def,
       assert_def, check_def, ignore_bind_def, return_def] >>
  simp[Once evaluate_def, Once evaluate_def, bind_assoc] >>
  gvs[bind_def, evaluate_type_builtin_def, evaluate_convert_from_def,
      evaluate_convert_def, lift_sum_def, return_def, assert_def,
      AllCaseEqs()]
QED

Theorem conditional_local_uint256_source:
  lookup_scopes x es.scopes = SOME ex /\
  lookup_scopes y es.scopes = SOME ey /\
  ex.value = IntV ix /\ ey.value = IntV iy /\
  within_int_bound (Unsigned 256) ix /\ within_int_bound (Unsigned 256) iy ==>
  bind (eval_expr cx
    (IfExp (BaseT (UintT 256)) (Literal (BaseT BoolT) (BoolL b))
      (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
        [Name (BaseT (UintT 256)) x])
      (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
        [Name (BaseT (UintT 256)) y]))) (read_result cx) es =
    (INL (IntV (if b then ix else iy)),es)
Proof
  strip_tac >> irule bool_literal_selected_value >> Cases_on `b` >> simp[] >>
  irule uint256_convert_value >> simp[expr_type_def] >>
  metis_tac[eval_name_word]
QED

Theorem lower_value_uint256_convert_child:
  expr_type e = BaseT (UintT 256) /\
  lower_value compile_expr cenv ty
    (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256)) [e]) sa =
    (op,sb) ==>
  lower_value compile_expr cenv (BaseT (UintT 256)) e sa = (op,sb)
Proof
  strip_tac >>
  `~is_bytestring_type (expr_type e)` by simp[is_bytestring_type_def] >>
  drule_all lower_value_convert >> strip_tac >>
  gvs[uint256_convert_forward]
QED

Theorem converted_local_enriched_path:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_scopes name es.scopes = SOME entry /\ entry.value = IntV i /\
  lower_value compile_expr cenv ty
    (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
      [Name (BaseT (UintT 256)) name]) sa = (op,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H tm t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
    expr_post ctx fn cenv cx
      (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
        [Name (BaseT (UintT 256)) name]) es sa sb s
      (es with gas_obs := []) entry.value op t /\
    ghost_inv d cenv cx (es with gas_obs := []) H tm t /\
    ghost_kept cenv es sa G tn s H tm /\ op_taint tm op = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ op_prov H op = NONE
Proof
  strip_tac >> drule_at (Pat `lower_value _ _ _ _ _ = _`)
    lower_value_uint256_convert_child >>
  simp[expr_type_def] >> strip_tac >>
  `is_word_type (BaseT (UintT 256))` by simp[is_word_type_def] >>
  drule_all lower_value_name_word >> strip_tac >>
  `?out. op = Var out` by
    (gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def] >> metis_tac[]) >>
  gvs[] >>
  `word_value entry.value` by simp[word_value_def] >>
  drule_all local_name_enriched_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `tm`, `t`] >> simp[] >>
  irule uint256_convert_post >> gvs[expr_type_def]
QED

Theorem converted_local_enriched_outcome:
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  lookup_scopes name es.scopes = SOME entry /\ entry.value = IntV i /\
  within_int_bound (Unsigned 256) i /\
  lower_value compile_expr cenv ty
    (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
      [Name (BaseT (UintT 256)) name]) sa = (op,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (eval_expr cx
      (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
        [Name (BaseT (UintT 256)) name])) (read_result cx)) (es,s,G,tn)
    (\res ee H tm t. ?v. res = INL v /\
      expr_post ctx fn cenv cx
        (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
          [Name (BaseT (UintT 256)) name]) es sa sb s ee v op t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee H tm t /\
      ptr_val_ok cx (BaseT (UintT 256)) v op H tm t /\
      (~is_word_type (BaseT (UintT 256)) ==>
        ptr_buf_ok cenv (TypeBuiltin (BaseT (UintT 256)) Convert
          (BaseT (UintT 256)) [Name (BaseT (UintT 256)) name]) op H t) /\
      ghost_kept cenv es sa G tn s H tm /\ op_prov H op = NONE)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all converted_local_enriched_path >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  rewrite_tac[fragGasPathPtrTheory.gas_outcome_ptr_def] >>
  qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[fragGasPathPtrTheory.gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL entry.value`, `es`, `H`, `tm`, `OK t`] >>
  simp[gasSummaryTheory.gas_explicit_def, bodyPtrDefsTheory.ptr_val_ok_def,
       is_word_type_def] >> reverse conj_tac >- gvs[] >> gen_tac >>
  `eval_expr cx (TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
      [Name (BaseT (UintT 256)) name]) (es with gas_obs := tail) =
      (INL (Value (IntV i)), es with gas_obs := tail)` by
    (irule uint256_convert_value >> simp[expr_type_def] >>
     `lookup_scopes name (es with gas_obs := tail).scopes = SOME entry` by simp[] >>
     pop_assum (mp_tac o MATCH_MP eval_name_word) >>
     disch_then (qspecl_then [`cx`, `BaseT (UintT 256)`] mp_tac) >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  gvs[bind_def, read_result_def, return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED
