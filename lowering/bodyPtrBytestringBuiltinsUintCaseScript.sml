Theory bodyPtrBytestringBuiltinsUintCase
Ancestors
  bodyPtrBytestringBuiltinsUnary bodyPtrBytestringBuiltinsUintCompile
  bodyPtrBytestringBuiltinsEval bodyPtrBytestringBuiltinsPrefix
  context fragGasPathPtr exprLoweringProps bodyPtrDefs exprWordOperand stmtFragPtr exprSimCalldataSlice wordArgsPtr exprSimWordArgs vyperTyping words integer vyperState valueEncoding vyperValue arithmetic loweringSlice
  bodyPtrPreds exprPtrUnwrap exprSimHypsDefs exprSimUint2Str
  exprLowering exprBopLowering exprSimSource compileEnv fragExec vyperAST vyperContext list

Theorem uint2str_body_operand_ptr:
  (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
    body_exprs_ptr_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Uint2Str n) args) es ==>
  ?e k. args = [e] /\ ann = BaseT (StringT n) /\
    expr_type e = BaseT (UintT k) /\ 78 <= n /\
    expr_body_pre cenv cx env e es /\
    expr_sim_ptr d ctx PG func cenv cx cty e es
Proof
  strip_tac >>
  `well_typed_expr env (Builtin ann (Uint2Str n) args)` by
    fs[expr_body_pre_def] >>
  drule uint2str_expr_types >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx [e]` by fs[builtin_args_length_ok_def] >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> fs[expr_body_pre_def]) >>
  simp[] >>
  fs[body_exprs_ptr_ok_def, body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem uint2str_compile_cut:
  compile_expr cenv ty (Builtin ann (Uint2Str n) [e]) sa = (vv,sb) ==>
  ?op sm. lower_value compile_expr cenv ty e sa = (op,sm) /\
    as_ptr_val ann LocMemory
      (compile_uint2str op n (type_memory_bytes cenv ann) sm) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> Uint2Str n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (Uint2Str n) [e]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  pairarg_tac >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem uint2str_code_appends:
  cs_appends (\sm. as_ptr_val ann LocMemory
    (compile_uint2str x n N sm))
Proof
  rw[cs_appends_def] >>
  Cases_on `compile_uint2str x n N sm` >> gvs[as_ptr_val_def] >>
  mp_tac (Q.INST [`op` |-> `x`, `sz` |-> `N`] uint2str_suffix_appends) >>
  simp[cs_appends_def] >> metis_tac[]
QED

Theorem uint2str_operand_endpoint:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT k) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  ?a. v = IntV (&a) /\ a < dimword(:256) /\
    eval_operand op t = SOME (n2w a) /\ expr_sim_inv cenv cx env ee
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all operand_eval_evidence_semantics >> strip_tac >>
  `?i. v = IntV i /\ 0 <= i /\ Num i < 2 ** k /\
       k <= 256 /\ 0 < k /\ k MOD 8 = 0` by
    (fs[is_word_type_def, evaluate_type_def] >> Cases_on `v` >>
     gvs[is_word_type_def, evaluate_type_def, value_has_type_def]) >>
  gvs[] >> qexists_tac `Num i` >> simp[] >>
  conj_tac
  >- (rewrite_tac[dimword_def] >>
      irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >>
      simp[EXP_BASE_LE_MONO]) >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  drule expr_post_word_operand >>
  simp[is_word_type_def, evaluate_type_def, word_value_def, val_to_w256_def,
    integer_wordTheory.i2w_def]
QED

Theorem uint2str_operand_suffix:
  expr_body_pre cenv cx env
    (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT k) /\ 78 <= n /\
  lower_value compile_expr cenv ty e sa = (op,sm) /\
  compile_uint2str op n (type_memory_bytes cenv (BaseT (StringT n))) sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
  ghost_inv d cenv cx ee G tn t /\
  ptr_val_ok cx (expr_type e) v op G tn t /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  ?a Gf tnf u. v = IntV (&a) /\
    gas_path_ptr D 0 ctx func PG G tn t 0 Gf tnf (OK u) /\
    ghost_inv d cenv cx ee Gf tnf u /\ ghost_kept cenv ee sm G tn t Gf tnf /\
    vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
      ee sm sb t ee (Value (StringV (num_to_dec_string a)))
      (LocatedValue (BaseT (StringT n))
        <|ptr_operand := out; ptr_location := LocMemory|>) u /\
    ptr_vv_ok cx (BaseT (StringT n)) (Value (StringV (num_to_dec_string a)))
      (LocatedValue (BaseT (StringT n))
        <|ptr_operand := out; ptr_location := LocMemory|>) ee Gf tnf u /\
    ptr_buf_ok cenv (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) out Gf u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all uint2str_operand_endpoint >> strip_tac >> gvs[] >>
  drule_all (SRULE [] (Q.INST
    [`sz` |-> `type_memory_bytes cenv (BaseT (StringT n))`]
    u2s_builtin_result_requirements)) >> strip_tac >>
  drule expr_post_state >> strip_tac >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    metis_tac[expr_body_pre_var_types_well_formed] >>
  `!z. op = Var z ==> not_fresh_at sm z` by
    (drule lower_value_word_shape >> disch_then (qspec_then `env` mp_tac) >>
     simp[is_word_type_def] >>
     impl_tac >- (fs[expr_body_pre_def] >> metis_tac[]) >>
     strip_tac >> metis_tac[]) >>
  drule (CONJUNCT2 compile_expr_grows) >> strip_tac >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  drule_all compile_uint2str_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  simp[expr_type_def] >> metis_tac[]
QED

Theorem uint2str_eval_continuation:
  expr_body_pre cenv cx env
    (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT k) /\ 78 <= n /\
  lower_value compile_expr cenv ty e sa = (op,sm) /\
  as_ptr_val (BaseT (StringT n)) LocMemory
    (compile_uint2str op n (type_memory_bytes cenv (BaseT (StringT n))) sm) = (vv,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
  ghost_inv d cenv cx ee G tn t /\
  ptr_val_ok cx (expr_type e) v op G tn t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vst. ((case builtin_result cx vst.accounts (BaseT (StringT n)) (Uint2Str n)
      [expr_type e] [v] of INL w => INL (Value w) | INR exc => INR exc), vst))
    (ee,t,G,tn)
    (\res ef Gf tnf u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
        es sa sb s0 ef tv vv u /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef Gf tnf u /\
      ptr_vv_ok cx (expr_type (Builtin (BaseT (StringT n)) (Uint2Str n) [e]))
        tv vv ef Gf tnf u /\
      (!t' x. vv = StackValue t' x /\
        ~is_word_type (expr_type (Builtin (BaseT (StringT n)) (Uint2Str n) [e])) ==>
        ptr_buf_ok cenv (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) x Gf u) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) p.ptr_operand Gf u) /\
      ghost_kept cenv es sa G0 tn0 s0 Gf tnf)
    (\res ef gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_uint2str op n (type_memory_bytes cenv (BaseT (StringT n))) sm` >>
  rename1 `compile_uint2str _ _ _ _ = (out,fin)` >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >>
  simp[as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  drule_all uint2str_operand_suffix >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule_all operand_prefix_frame_inputs >> strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_wb_trans >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `vv_post ctx func cenv cx (Builtin (BaseT (StringT n)) (Uint2Str n) [e])
      es sa fin s0 ee (Value (StringV (num_to_dec_string a)))
      (LocatedValue (BaseT (StringT n))
        <|ptr_operand := out; ptr_location := LocMemory|>) u` by
    (irule vv_post_prefix_frame >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ee with gas_obs := [] = ee` by
    (qpat_x_assum `?marks ee0. _` strip_assume_tac >> simp[]) >>
  simp[gas_outcome_ptr_def, gas_summary_ptr_at_def, uint2str_source_result,
      expr_type_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INL (Value (StringV (num_to_dec_string a)))`, `ee`, `Gf`, `tnf`, `OK u`] >>
  qpat_x_assum `vv_post _ _ _ _ _ es sa fin s0 _ _ _ _` mp_tac >>
  once_rewrite_tac[vv_post_located_mk_ptr] >>
  simp[ptr_vv_ok_def, mk_ptr_def] >>
  fs[ptr_vv_ok_def]
QED

Theorem uint2str_body_expr_ptr_ok:
  !cx ann n args.
    (builtin_args_length_ok (Uint2Str n) (LENGTH args) ==>
      body_exprs_ptr_ok cx args) ==>
    body_expr_ptr_ok cx (Builtin ann (Uint2Str n) args)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all uint2str_body_operand_ptr >>
  disch_then (qspecl_then [`func`, `d`, `ty`, `PG`] strip_assume_tac) >> gvs[] >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es` suffices_by
    metis_tac[expr_sim_ptr_of_vv] >>
  irule compile_unary_builtin_eval_vv_sim_ptr >>
  simp[vyperInterpreterTheory.precompile_builtin_def, builtin_args_length_ok_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`\x sm. as_ptr_val (BaseT (StringT n)) LocMemory
      (compile_uint2str x n (type_memory_bytes cenv (BaseT (StringT n))) sm)`, `ty`] >>
  simp[uint2str_code_appends] >>
  reverse conj_tac >- metis_tac[uint2str_compile_cut] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule uint2str_eval_continuation >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED
