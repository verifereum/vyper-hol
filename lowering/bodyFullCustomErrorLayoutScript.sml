(* Compiler cuts for the shared custom-error fragment and its assert branch. *)
Theory bodyFullCustomErrorLayout
Ancestors
  fragExec loweringPosts stmtLoweringMono
  stmtLowering exprLoweringProps emitHelper emitHelperProps compileEnv vyperAST
  gasShadow gasShadowState gasShadowCompileStmtHelpers bodyFullShared
  gasShadowCompileHelpers gasShadowCompile gasShadowCompilePure
  stmtSimCustomErrorRevert loweringHalt list pair

Theorem stmt_env_raise_custom[local]:
  stmt_env cenv lctx ty (Raise (RaiseCustomError err)) sa = (ce,sb) <=>
  ce = cenv /\ compile_revert_with_custom_error cenv err sa = ((),sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, Once compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> metis_tac[]
QED

Theorem compile_assert_custom_parts[local]:
  stmt_env cenv lctx ty (Assert e (AssertCustomError err)) sa = (ce,sb) ==>
  ?op s1 ok s2 fl s3 s4 entry last.
    ce = cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,entry) /\
    stmt_env cenv lctx ty (Raise (RaiseCustomError err)) entry = (cenv,last) /\
    new_block ok last = (last.cs_current_bb,sb)
Proof
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `lower_value compile_expr cenv (BaseT BoolT) e sa` >>
  rename1 `_ = (op,s1)` >> simp[] >>
  Cases_on `fresh_label "assert_ok" s1` >> rename1 `_ = (ok,s2)` >> simp[] >>
  Cases_on `fresh_label "assert_fail" s2` >> rename1 `_ = (fl,s3)` >> simp[] >>
  Cases_on `emit_inst JNZ [op; Label ok; Label fl] [] s3` >>
  rename1 `_ = (u,s4)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block fl s4` >> rename1 `_ = (v,entry)` >> simp[] >>
  Cases_on `compile_revert_with_custom_error cenv err entry` >>
  rename1 `_ = (u,last)` >> Cases_on `u` >> simp[] >>
  Cases_on `new_block ok last` >> rename1 `_ = (x,sb1)` >>
  simp[] >> strip_tac >> gvs[] >>
  imp_res_tac new_block_props >> gvs[]
QED

Theorem assert_custom_compiler_code[local]:
  lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (x5,entry) /\
  stmt_env cenv lctx ty (Raise (RaiseCustomError err)) entry = (cenv,last) /\
  new_block ok last = (x7,sb) /\ fn_has_code sa sb func ==>
  fn_has_code sa s1 func /\ fn_has_code s3 s4 func /\
  fn_has_code entry last func /\
  s3.cs_current_bb = s1.cs_current_bb /\
  s3.cs_current_insts = s1.cs_current_insts /\
  entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
  sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
  sa.cs_next_var <= entry.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var
Proof
  strip_tac >> drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends entry last /\ entry.cs_next_var <= last.cs_next_var` by
    (`compile_stmt cenv lctx ty (Raise (RaiseCustomError err)) entry = ((),last)` by
       fs[stmt_env_raise_custom, Once compile_stmt_def] >>
     mp_tac (Q.SPECL [`cenv`,`lctx`,`ty`,`Raise (RaiseCustomError err)`]
       (cj 1 compile_stmt_cs_mono)) >>
     rw[cs_mono_def] >> first_x_assum (qspec_then `entry` mp_tac) >> simp[]) >>
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
  `cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s4 /\
   cs_extends s4 entry /\ cs_extends last sb` by
    metis_tac[cs_extends_fresh_label, cs_extends_new_block, cs_extends_emit_inst] >>
  `s3.cs_next_var = s4.cs_next_var` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, comp_return_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  simp[] >>
  rpt conj_tac >> TRY decide_tac >>
  irule fn_has_code_mid >> metis_tac[cs_extends_trans, cs_extends_refl]
QED

Theorem compile_assert_custom_layout_full:
  !sd.
  stmt_env cenv lctx ty (Assert e (AssertCustomError err)) sa = (ce,sb) /\
  stmt_env (gas_shadow_env sd cenv) lctx ty
    (Assert (gas_shadow_expr e) (AssertCustomError (gas_shadow_custom_error err)))
    ta = (ct,tb) /\
  gas_shadow_state sa ta /\ fn_has_code sa sb func /\ fn_has_code ta tb sfunc ==>
  ?op s1 ok s2 fl s3 s4 entry last t1 t2 t3 t4 sentry slast.
    ce = cenv /\ ct = gas_shadow_env sd cenv /\
    lower_value compile_expr cenv (BaseT BoolT) e sa = (op,s1) /\
    fresh_label "assert_ok" s1 = (ok,s2) /\
    fresh_label "assert_fail" s2 = (fl,s3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (s4.cs_current_bb,entry) /\
    stmt_env cenv lctx ty (Raise (RaiseCustomError err)) entry = (cenv,last) /\
    new_block ok last = (last.cs_current_bb,sb) /\
    lower_value compile_expr (gas_shadow_env sd cenv) (BaseT BoolT)
      (gas_shadow_expr e) ta = (op,t1) /\
    fresh_label "assert_ok" t1 = (ok,t2) /\
    fresh_label "assert_fail" t2 = (fl,t3) /\
    emit_inst JNZ [op; Label ok; Label fl] [] t3 = ((),t4) /\
    new_block fl t4 = (t4.cs_current_bb,sentry) /\
    stmt_env (gas_shadow_env sd cenv) lctx ty
      (Raise (RaiseCustomError (gas_shadow_custom_error err))) sentry =
        (gas_shadow_env sd cenv,slast) /\
    new_block ok slast = (slast.cs_current_bb,tb) /\
    gas_shadow_state s1 t1 /\ gas_shadow_state entry sentry /\
    gas_shadow_state last slast /\
    fn_has_code sa s1 func /\ fn_has_code s3 s4 func /\
    fn_has_code entry last func /\
    s3.cs_current_bb = s1.cs_current_bb /\
    s3.cs_current_insts = s1.cs_current_insts /\
    entry.cs_current_bb = fl /\ entry.cs_current_insts = [] /\
    sb.cs_current_bb = ok /\ sb.cs_current_insts = [] /\
    sa.cs_next_var <= entry.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
    fn_has_code ta t1 sfunc /\ fn_has_code t3 t4 sfunc /\
    fn_has_code sentry slast sfunc /\
    t3.cs_current_bb = t1.cs_current_bb /\
    t3.cs_current_insts = t1.cs_current_insts /\
    sentry.cs_current_bb = fl /\ sentry.cs_current_insts = [] /\
    tb.cs_current_bb = ok /\ tb.cs_current_insts = [] /\
    ta.cs_next_var <= sentry.cs_next_var /\ ta.cs_next_var <= tb.cs_next_var
Proof
  rpt strip_tac >>
  qpat_assum `stmt_env _ _ _ (Assert e _) _ = _`
    (mp_then Any (qx_choosel_then [`op`,`s1`,`ok`,`s2`,`fl`,`s3`,
      `s4`,`entry`,`last`] strip_assume_tac) compile_assert_custom_parts) >>
  qpat_assum `stmt_env _ _ _ (Assert (gas_shadow_expr e) _) _ = _`
    (mp_then Any (qx_choosel_then [`op'`,`t1`,`ok'`,`t2`,`fl'`,`t3`,
      `t4`,`sentry`,`slast`] strip_assume_tac) compile_assert_custom_parts) >>
  `op' = op /\ gas_shadow_state s1 t1` by
    metis_tac[gas_shadow_step, gas_shadow_stmt_lower_value_env] >> gvs[] >>
  `ok' = ok /\ gas_shadow_state s2 t2` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >> gvs[] >>
  `fl' = fl /\ gas_shadow_state s3 t3` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_fresh_label] >> gvs[] >>
  `gas_shadow_state s4 t4` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_emit_inst] >>
  `gas_shadow_state entry sentry` by
    metis_tac[gas_shadow_step, gas_shadow_compiles_new_block] >>
  `gas_shadow_state last slast` by
    (fs[stmt_env_raise_custom] >>
     metis_tac[gas_shadow_step, gas_shadow_compile_revert_with_custom_error]) >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `x5` |-> `s4.cs_current_bb`,
    `x7` |-> `last.cs_current_bb`] assert_custom_compiler_code) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  mp_tac (Q.INST [`cenv` |-> `gas_shadow_env sd ce`,
    `e` |-> `gas_shadow_expr e`,
    `err` |-> `gas_shadow_custom_error err`,
    `sa` |-> `ta`, `sb` |-> `tb`, `func` |-> `sfunc`,
    `s1` |-> `t1`, `s2` |-> `t2`, `s3` |-> `t3`, `s4` |-> `t4`,
    `entry` |-> `sentry`, `last` |-> `slast`,
    `x5` |-> `t4.cs_current_bb`, `x7` |-> `slast.cs_current_bb`]
    assert_custom_compiler_code) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  qexistsl_tac [`s4`,`entry`,`last`,`t4`,`sentry`,`slast`] >> simp[]
QED

Theorem custom_error_compile_args_mono[local]:
  compile_ext_call_args compile_expr ce [] tys args sa = (saved,sb) ==>
  ci_mono sa sb
Proof
  strip_tac >>
  qspecl_then [`args`,`tys`,`compile_expr`,`ce`,`[]`,`sa`] mp_tac
    ci_mono_compile_ext_call_args >>
  simp[cj 1 compile_expr_ci_mono]
QED

Theorem custom_error_compile_args_shadow[local]:
  gas_shadow_compiles
    (compile_ext_call_args compile_expr ce [] tys args)
    (compile_ext_call_args compile_expr ce [] tys (MAP gas_shadow_expr args))
Proof
  mp_tac (REWRITE_RULE [gasShadowCompileBaseTheory.gas_shadow_env_F]
    (Q.INST [`sd` |-> `F`, `sh` |-> `T`, `cenv` |-> `ce`]
      (MATCH_MP gas_shadow_compiles_ext_call_args
        (cj 1 gas_shadow_compile_expr_env)))) >>
  disch_then (qspecl_then [`args`,`[]`,`tys`] mp_tac) >> simp[]
QED

Theorem custom_error_encoder_extends[local]:
  compile_abi_encode_values_to_buf c p rows a = (len,b) ==> cs_extends a b
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`c`,`p`,`rows`,`a`] ci_mono_compile_abi_encode_values_to_buf) >>
  asm_rewrite_tac [pairTheory.SND, ci_mono_def] >> simp[]
QED

Theorem compile_raise_custom_layout_full:
  ce.ce_error_info (nsid_to_string id) = SOME params /\
  args = custom_error_exprs (CustomError id pos kw) /\
  tys = MAP (lowered_value_type ce) args /\
  stmt_env ce lctx ty (Raise (RaiseCustomError (CustomError id pos kw))) sa = (ca,sb) /\
  stmt_env ce lctx ty
     (Raise (RaiseCustomError (gas_shadow_custom_error (CustomError id pos kw))))
     ta = (ct,tb) /\
  gas_shadow_state sa ta /\ fn_has_code sa sb func /\ fn_has_code ta tb sfunc ==>
  ?saved se te buf sm ss.
    ca = ce /\ ct = ce /\
    compile_ext_call_args compile_expr ce [] tys args sa = (saved,se) /\
    compile_ext_call_args compile_expr ce [] tys (MAP gas_shadow_expr args) ta = (saved,te) /\
    gas_shadow_state se te /\ fn_has_code sa se func /\ fn_has_code ta te sfunc /\
    ci_mono sa se /\
    compile_alloc_buffer (abi_size_bound ce.ce_struct_fields (TupleT tys) + 32)
      se = (buf,sm) /\
    emit_void MSTORE
      [buf.buf_operand; Lit (n2w (ce.ce_method_id (SND id) (MAP SND params)))]
      sm = ((),ss) /\
    fn_has_code se sm func /\ fn_has_code sm ss func /\
    (if NULL args then
       ?offset sn. emit_op ADD [buf.buf_operand; Lit 28w] ss = (offset,sn) /\
                   emit_inst REVERT [offset; Lit 4w] [] sn = ((),sb) /\
                   fn_has_code ss sn func /\ fn_has_code sn sb func
     else
       ?dst st encoded en offset sr len sn.
         emit_op ADD [buf.buf_operand; Lit 32w] ss = (dst,st) /\
         compile_abi_encode_values_to_buf ce dst (ZIP (saved,tys)) st = (encoded,en) /\
         emit_op ADD [buf.buf_operand; Lit 28w] en = (offset,sr) /\
         emit_op ADD [Lit 4w; encoded] sr = (len,sn) /\
         emit_inst REVERT [offset; len] [] sn = ((),sb) /\
         fn_has_code ss st func /\ fn_has_code st en func /\
         fn_has_code en sr func /\ fn_has_code sr sn func /\ fn_has_code sn sb func)
Proof

  strip_tac >> fs[stmt_env_raise_custom] >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `positional` |-> `pos`, `kwargs` |-> `kw`,
     `s0` |-> `sa`, `s1` |-> `sb`] compile_revert_with_custom_error_split) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`saved`,`se`,`buf`,`sm`,`ss`] strip_assume_tac) >>
  `?saved' te tbuf tm ts.
    compile_ext_call_args compile_expr ce [] tys (MAP gas_shadow_expr args) ta = (saved',te) /\
    compile_alloc_buffer (abi_size_bound ce.ce_struct_fields (TupleT tys) + 32)
      te = (tbuf,tm) /\
    emit_void MSTORE
      [tbuf.buf_operand; Lit (n2w (ce.ce_method_id (SND id) (MAP SND params)))]
      tm = ((),ts) /\
    (if NULL args then
       ?offset sn. emit_op ADD [tbuf.buf_operand; Lit 28w] ts = (offset,sn) /\
                   emit_inst REVERT [offset; Lit 4w] [] sn = ((),tb)
     else
       ?dst st encoded en offset sr len sn.
         emit_op ADD [tbuf.buf_operand; Lit 32w] ts = (dst,st) /\
         compile_abi_encode_values_to_buf ce dst (ZIP (saved',tys)) st = (encoded,en) /\
         emit_op ADD [tbuf.buf_operand; Lit 28w] en = (offset,sr) /\
         emit_op ADD [Lit 4w; encoded] sr = (len,sn) /\
         emit_inst REVERT [offset; len] [] sn = ((),tb))` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `args` |-> `MAP gas_shadow_expr args`,
        `positional` |-> `MAP gas_shadow_expr pos`,
        `kwargs` |-> `MAP (I ## gas_shadow_expr) kw`,
        `s0` |-> `ta`, `s1` |-> `tb`] compile_revert_with_custom_error_split) >>
     simp[GSYM gas_shadow_custom_error_exprs, GSYM gas_shadow_custom_error_def,
          MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss, NULL_EQ]) >>
  `saved' = saved /\ gas_shadow_state se te` by
    metis_tac[gas_shadow_step, custom_error_compile_args_shadow] >> gvs[] >>
  `ci_mono sa se /\ cs_extends ta te /\ cs_extends se sm /\
     cs_extends sm ss /\ cs_extends te tm /\ cs_extends tm ts` by
    metis_tac[custom_error_compile_args_mono, ci_mono_def, compile_alloc_buffer_extends,
              cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends sa se` by fs[ci_mono_def] >>
  Cases_on `NULL (custom_error_exprs (CustomError id pos kw))` >> gvs[] >>
  imp_res_tac cs_extends_emit_inst >>
  imp_res_tac (REWRITE_RULE [cs_appends_def] (cj 2 cs_appends_emit_helpers)) >>
  imp_res_tac custom_error_encoder_extends >>
  NTAC 3 (imp_res_tac cs_extends_trans) >>
  `fn_has_code sa se func /\ fn_has_code se sm func /\
    fn_has_code sm ss func` by
    (rpt conj_tac >> irule fn_has_code_mid >>
     simp[] >> qexistsl_tac [`sb`,`sa`] >> simp[cs_extends_refl]) >>
  `fn_has_code ta te sfunc` by
    (irule fn_has_code_mid >> simp[] >>
     qexistsl_tac [`tb`,`ta`] >> simp[cs_extends_refl]) >>
  simp[] >> rpt conj_tac >>
  irule fn_has_code_mid >> simp[] >>
  qexistsl_tac [`sb`,`sa`] >> simp[cs_extends_refl]
QED
