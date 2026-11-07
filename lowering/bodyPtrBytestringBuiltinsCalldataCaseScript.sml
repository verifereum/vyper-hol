Theory bodyPtrBytestringBuiltinsCalldataCase
Ancestors
  bodyPtrBytestringBuiltinsEval bodyPtrBytestringBuiltinsExternalSlice
  bodyPtrPreds exprPtrUnwrap vyperTypeSystem exprSimHypsDefs
  emitHelperProps compileEnv fragExec bodyPtrBytestringBuiltinsCalldataOutcome
  exprSimWordArgs loweringPosts bodyPtrDefs exprOperandVar
  exprLoweringProps stmtLoweringMono allocLimits valueEncoding
  valueEncodingProps vfmConstants words vyperAST vyperTyping vyperValue
  immutableEncodingProofs vyperTypeInvariants vyperLoweringCorrect vyperTypeContractSoundness
  vyperInterpreter bodyPtrBytestringBuiltinsPrefix gasSummaryComposePtr
  exprSimCalldataSlice exprSimUint2Str wordArgsPtr stmtFragPtr context
  vyperContext exprSimSource exprLowering exprBopLowering list

(* Expose the actual lowered operand from the conditional body hypothesis.
   Typing, rather than an unconditional list membership rule, fixes arity. *)
Theorem calldata_slice_body_operand_ptr:
  (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
    body_exprs_ptr_ok cx args) /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
  ?e. args = [e] /\ expr_type e = BaseT (UintT 256) /\
    ann = BaseT (BytesT (Dynamic n)) /\ 0 < n /\ n < 2 ** 256 /\
    expr_body_pre cenv cx env e es /\
    expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es
Proof
  strip_tac >>
  `well_typed_expr env (Builtin ann (CalldataSlice n) args)` by
    fs[expr_body_pre_def] >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  strip_tac >> Cases_on `args` >> gvs[] >>
  `body_expr_ptr_ok cx h` by
    fs[builtin_args_length_ok_def, body_exprs_ptr_ok_def] >>
  `expr_body_pre cenv cx env h es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> fs[expr_body_pre_def]) >>
  fs[body_expr_ptr_ok_def] >> metis_tac[]
QED

(* Consumer-facing equation: hide dispatch and expose only the operand and
   the already checked calldata fragment, without a let-bound statement. *)
Theorem calldata_slice_compile_cut:
  compile_expr cenv ty (Builtin ann (CalldataSlice n) [e]) sa = (vv,sb) ==>
  ?op sm. lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
    as_ptr_val ann LocMemory
      (compile_slice_calldata op (Lit (n2w n))
        (type_memory_bytes cenv ann) sm) = (vv,sb)
Proof
  `!bt args. names_builtin bt args ==> bt <> CalldataSlice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `~names_builtin (CalldataSlice n) [e]` by metis_tac[] >>
  simp[compile_expr_builtin_dispatch] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, vyperASTTheory.expr_size_def, list_size_def] >>
  pairarg_tac >> simp[] >> strip_tac >> metis_tac[]
QED

Theorem calldata_slice_code_appends:
  cs_appends (\sm. as_ptr_val ann LocMemory
    (compile_slice_calldata x (Lit (n2w n)) N sm))
Proof
  rw[cs_appends_def] >>
  Cases_on `compile_slice_calldata x (Lit (n2w n)) N sm` >>
  gvs[as_ptr_val_def] >>
  drule compile_slice_calldata_stages >> strip_tac >>
  metis_tac[cs_extends_trans]
QED


Theorem calldata_slice_operand_static_cut:
  lower_value compile_expr cenv cty e sa = (op,sm) /\
  local_ptrs_reserved cenv sa ==>
  (!z. op = Var z ==> not_fresh_at sm z) /\
  sa.cs_next_var <= sm.cs_next_var
Proof
  strip_tac >>
  `ci_mono sa (SND (lower_value compile_expr cenv cty e sa))` by
    (irule ci_mono_lower_value_cfn >>
     simp[cj 1 ci_mono_compile_expr_sa]) >>
  conj_tac >- metis_tac[compile_lower_value_var] >>
  gvs[ci_mono_def]
QED

Theorem calldata_slice_result_requirements:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) args) es /\
  N = type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) ==>
  ~is_word_type (expr_type (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) args)) /\
  evaluate_type (get_tenv cx)
    (expr_type (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) args)) =
      SOME (BaseTV (BytesT (Dynamic n))) /\
  type_memory_bytes cenv
    (lowered_value_type cenv (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) args)) = N /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) = N /\
  32 + n <= N /\ N < dimword (:256) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n (DROP a bs)))
Proof
  strip_tac >>
  `N < 2 ** 64` by
    fs[expr_body_pre_def, alloc_limits_expr_def, type_alloc_ok_def, is_word_type_def] >>
  `n <= 32 * ((n + 31) DIV 32)` by
    metis_tac[immutable_capacity_roundup, word_size_def] >>
  `LENGTH (TAKE n (DROP a bs)) <= n` by
    simp[LENGTH_TAKE_EQ] >>
  gvs[type_memory_bytes_def] >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def, lowered_value_type_def,
    type_memory_size_def, type_slot_size_def, type_memory_bytes_def,
    word_size_def, val_wf_def, dimword_def] >> decide_tac
QED

Theorem calldata_slice_operand_source_outcome:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  0 < n /\ n < dimword (:256) /\
  lower_value compile_expr cenv cty e sa = (op,sm) /\
  compile_slice_calldata op (Lit (n2w n))
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm = (out,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
  ghost_inv d cenv cx ee G tn t /\ ptr_val_ok cx (expr_type e) v op G tn t /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (\vst. ((case builtin_result cx vst.accounts (BaseT (BytesT (Dynamic n)))
      (CalldataSlice n) [expr_type e] [v] of
      INL w => INL (Value w) | INR exc => INR exc), vst)) (ee,t,G,tn)
    (\res ef H tm u. ?w. res = INL (Value w) /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) ee sm sb t ef (Value w)
        (LocatedValue (BaseT (BytesT (Dynamic n)))
          <|ptr_operand := out; ptr_location := LocMemory|>) u /\
      ptr_vv_ok cx (BaseT (BytesT (Dynamic n))) (Value w)
        (LocatedValue (BaseT (BytesT (Dynamic n)))
          <|ptr_operand := out; ptr_location := LocMemory|>) ef H tm u /\
      ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) out H u /\
      ghost_inv d cenv cx ef H tm u /\ ghost_kept cenv ee sm G tn t H tm /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~u.vs_halted)
    (\res ef gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_slice_operand_endpoint >> strip_tac >> gvs[] >>
  drule_all calldata_slice_operand_static_cut >> strip_tac >>
  drule expr_post_state >> strip_tac >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `op_prov G op = NONE /\ op_taint tn op = {}` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  `cx.txn.calldata = t.vs_call_ctx.cc_calldata` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by
    fs[expr_sim_inv_def, context_well_typed_def, dimword_def] >>
  irule (SRULE [expr_type_def] (Q.INST
    [`e` |-> `Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]`]
    compile_slice_calldata_source_outcome)) >>
  simp[is_word_type_def] >>
  qexistsl_tac [`type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`,
    `a`, `n`, `op`] >>
  simp[builtin_result_def, evaluate_builtin_def, dimword_def] >>
  conj_tac >- (Cases_on `evaluate_calldata_slice t.vs_call_ctx.cc_calldata (IntV (&a)) n` >> simp[]) >>
  mp_tac (Q.INST [`N` |-> `type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))`,
    `a` |-> `a`, `bs` |-> `t.vs_call_ctx.cc_calldata`, `args` |-> `[e]`] calldata_slice_result_requirements) >>
  simp[expr_type_def, dimword_def] >> metis_tac[]
QED

Theorem calldata_slice_eval_continuation:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  0 < n /\ n < dimword (:256) /\
  lower_value compile_expr cenv cty e sa = (op,sm) /\
  as_ptr_val (BaseT (BytesT (Dynamic n))) LocMemory
    (compile_slice_calldata op (Lit (n2w n))
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm) = (vv,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
  ghost_inv d cenv cx ee G tn t /\ ptr_val_ok cx (expr_type e) v op G tn t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (?marks ee0. ee = ee0 with gas_obs := [] /\
    !tail. vyperState$bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v,ee0 with gas_obs := tail)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vst. ((case builtin_result cx vst.accounts (BaseT (BytesT (Dynamic n)))
      (CalldataSlice n) [expr_type e] [v] of
      INL w => INL (Value w) | INR exc => INR exc), vst)) (ee,t,G,tn)
    (\res ef H tm u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es sa sb s0 ef tv vv u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ef H tm u /\
      ptr_vv_ok cx (expr_type (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]))
        tv vv ef H tm u /\
      (!t' x. vv = StackValue t' x /\
        ~is_word_type (expr_type (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])) ==>
        ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) x H u) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) p.ptr_operand H u) /\
      ghost_kept cenv es sa G0 tn0 s0 H tm)
    (\res ef gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_slice_calldata op (Lit (n2w n))
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm` >>
  rename1 `compile_slice_calldata _ _ _ _ = (out,fin)` >>
  qpat_x_assum `as_ptr_val _ _ _ = _` mp_tac >> simp[as_ptr_val_def] >>
  disch_then (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
  drule_all calldata_slice_operand_source_outcome >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] assume_tac) >>
  drule_all operand_prefix_frame_inputs >> strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac gas_outcome_ptr_conseq) >>
  qpat_assum `expr_type e = _` (fn th => pure_rewrite_tac[th]) >>
  disch_then irule >>
  reverse conj_tac >- simp[] >>
  simp[expr_type_def, mk_ptr_def] >> rpt gen_tac >> strip_tac >>
  qexists_tac `Value w` >> simp[] >>
  conj_tac
  >- (irule vv_post_prefix_frame >> simp[] >>
      qexistsl_tac [`ee`, `sm`, `t`] >> simp[] >>
      qpat_x_assum `vv_post _ _ _ _ _ ee sm _ _ _ _ _ _` mp_tac >>
      once_rewrite_tac[vv_post_located_mk_ptr] >> simp[mk_ptr_def]) >>
  conj_tac >- fs[ptr_vv_ok_def] >>
  irule ghost_kept_wb_trans >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem calldata_slice_body_expr_ptr_ok:
  !cx ann n args.
    (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
      body_exprs_ptr_ok cx args) ==>
    body_expr_ptr_ok cx (Builtin ann (CalldataSlice n) args)
Proof
  rpt gen_tac >> disch_tac >> rewrite_tac[body_expr_ptr_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all calldata_slice_body_operand_ptr >>
  disch_then (qspecl_then [`func`, `d`, `PG`] strip_assume_tac) >> gvs[] >>
  `expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es` suffices_by
    metis_tac[expr_sim_ptr_of_vv] >>
  irule compile_unary_builtin_eval_vv_sim_ptr >>
  simp[precompile_builtin_def, builtin_args_length_ok_def] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`\x sm. as_ptr_val (BaseT (BytesT (Dynamic n))) LocMemory
    (compile_slice_calldata x (Lit (n2w n))
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm)`, `expr_type e`] >>
  simp[calldata_slice_code_appends] >>
  reverse conj_tac >- metis_tac[calldata_slice_compile_cut] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_type e = _` (fn th => rewrite_tac[GSYM th]) >>
  irule calldata_slice_eval_continuation >> goal_assum (drule_at Any) >>
  simp[dimword_def] >> metis_tac[]
QED
