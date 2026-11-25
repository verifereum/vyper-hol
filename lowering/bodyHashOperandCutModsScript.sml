(* Paired compiler cuts for the unary linked hash builtins. *)
Theory bodyHashOperandCutMods
Ancestors
  bodyFullPostsMods bodyFullPredsMods bodyFullShared bodySimFull
  exprSimHash exprSimHypsDefs exprSimSource exprLowering exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState gasShadow
  compileEnv fragExec loweringPosts vyperTyping vyperTypeSystem vyperAST
  vyperInterpreter vyperState vyperContext list exprBodyPreProps
  supportedExprTraverse allocLimits vyperTypeCallGraph constSubstCorrect
  gasOutcomeFullMods gasContext gasExplicitSites exprSimDefs bodyPtrDefs
  venomState ptrDiscipline

val hash_type = ``BaseT (BytesT (Fixed 32))``;
val hash_expr = ``Builtin ^hash_type b [e]``;
val hash_code = ``\m.
  if is_bytestring_type (expr_type e) then
    if b = vyperAST$Keccak256 then compile_keccak256_bytes x m else compile_sha256_bytes x m
  else case expr_type e of
    BaseT (BytesT (Fixed k)) =>
      if b = vyperAST$Keccak256 then compile_keccak256_bytesm x k m else compile_sha256_bytesm x k m
  | _ => if b = vyperAST$Keccak256 then compile_keccak256_word x m else compile_sha256_word x m``;

Theorem hash_stack_pair[local]:
  as_stack_val ty p = (StackValue ty op,sb) <=> p = (op,sb)
Proof
  Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem hash_compiler_suffix[local]:
  (b = vyperAST$Keccak256 \/ b = Sha256) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_expr cenv ty ^hash_expr sa = (StackValue ^hash_type op,sb) ==>
  ^hash_code sm = (op,sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ [_]) _ = _` mp_tac >>
  Cases_on `b = vyperAST$Keccak256` >> gvs[compile_hash_singleton, hash_stack_pair]
QED

Theorem hash_compiler_appends[local]:
  is_bytes_or_string_type (expr_type e) ==> cs_appends ^hash_code
Proof
  Cases_on `expr_type e` >> simp[is_bytes_or_string_type_def] >>
  rename1 `expr_type e = BaseT bt` >> Cases_on `bt` >>
  simp[is_bytes_or_string_type_def, is_bytestring_type_def] >>
  TRY (rename1 `expr_type e = BaseT (BytesT bd)` >> Cases_on `bd`) >>
  simp[is_bytestring_type_def] >> Cases_on `b = vyperAST$Keccak256` >>
  pure_rewrite_tac[cs_appends_def] >> BETA_TAC >>
  metis_tac[REWRITE_RULE [cs_appends_def] hash_suffix_appends]
QED

Theorem hash_compiler_cuts[local]:
  (b = vyperAST$Keccak256 \/ b = Sha256) /\ is_bytes_or_string_type (expr_type e) /\
  compile_expr cenv ty ^hash_expr sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^hash_expr) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x sm shadow_sm op.
    vv = StackValue ^hash_type op /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\
    ^hash_code sm = (op,sb) /\ ^hash_code shadow_sm = (op,shadow_sb) /\
    gas_shadow_state sm shadow_sm /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ e sa = (x,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr _) shadow_sa = (sx,shadow_sm)` >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
    simp[gas_shadow_stmt_lower_value_env] >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  `?op. vv = StackValue ^hash_type op` by
    (qpat_assum `compile_expr _ _ (Builtin _ _ [_]) _ = _` mp_tac >>
     Cases_on `b = vyperAST$Keccak256` >>
     gvs[compile_hash_singleton, exprBopLoweringTheory.as_stack_val_pair]) >>
  qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
  `^hash_code sm = (op,sb)` by (irule hash_compiler_suffix >> simp[] >> qexistsl_tac [`cenv`,`sa`,`ty`] >> simp[]) >>
  `^hash_code shadow_sm = (op,shadow_sb)` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     Cases_on `b = vyperAST$Keccak256` >>
     gvs[gas_shadow_expr_def, gas_shadow_builtin_def, compile_hash_singleton, hash_stack_pair]) >>
  `cs_appends ^hash_code` by (drule hash_compiler_appends >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (qpat_x_assum `cs_appends _` (strip_assume_tac o REWRITE_RULE [cs_appends_def]) >>
     conj_tac >> first_x_assum irule >> qexists_tac `op` >> first_assum ACCEPT_TAC) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    (irule fn_has_code_split >> simp[]) >>
  qexistsl_tac [`x`,`sm`,`shadow_sm`,`op`] >> simp[]
QED

Theorem hash_operand_shape[local]:
  (b = vyperAST$Keccak256 \/ b = Sha256) /\
  (builtin_args_length_ok b (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  expr_body_pre_mods mods cenv cx env (Builtin ann b args) es ==>
  ?e. args = [e] /\ ann = ^hash_type /\ is_bytes_or_string_type (expr_type e) /\
      body_expr_full_ok_mods mods exps cx e /\ expr_body_pre_mods mods cenv cx env e es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `well_typed_builtin_app ann b (MAP expr_type args)` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def]) >>
  `?t. MAP expr_type args = [t] /\ is_bytes_or_string_type t /\ ann = ^hash_type` by
    (drule_at Any hash_builtin_types >> Cases_on `b = vyperAST$Keccak256` >> gvs[]) >>
  Cases_on `args` >> gvs[builtin_args_length_ok_def] >>
  fs[body_exprs_full_ok_mods_def] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ _ _) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def, byte_widths_expr_def,
       alloc_limits_expr_def, int_calls_expr_def, expr_has_evm_run_thm,
       supported_expr_exists_def, DISJ_IMP_THM, FORALL_AND_THM, frame_well_typed_exprs_cons]
QED

Theorem hash_prefix_admissible[local]:
  (b = vyperAST$Keccak256 \/ b = Sha256) /\
  gas_admissible (eval_expr cx ^hash_expr) expr_vv_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `src = bind (eval_expr cx e) (read_result cx)` >>
  `?next. eval_expr cx ^hash_expr = bind src next` by
    (simp[Abbr `src`] >> Cases_on `b = vyperAST$Keccak256` >>
     gvs[eval_expr_unary_builtin_action, builtin_args_length_ok_def,
         is_self_codesize_def, eval_expr_sha256_action] >>
     qmatch_goalsub_abbrev_tac `bind _ cont = _` >> qexists_tac `cont` >> REFL_TAC) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def, expr_res_ok_def, expr_vv_res_ok_def]
QED

val child_post = ``\(H:(bool # 256 word # type_value) list # num list) (res:value + exception) ee G tn t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 ee v x t /\
  expr_store_bound cx (post_value_type cenv e) v x t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem hash_operand_cut_mods:
  (b = vyperAST$Keccak256 \/ b = Sha256) /\
  (builtin_args_length_ok b (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann b args) es /\
  compile_expr cenv ty (Builtin ann b args) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin ann b args)) shadow_sa = (vv,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  gas_admissible (eval_expr cx (Builtin ann b args)) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?e x sm shadow_sm op.
    args = [e] /\ ann = ^hash_type /\ vv = StackValue ^hash_type op /\
    is_bytes_or_string_type (expr_type e) /\ expr_body_pre_mods mods cenv cx env e es /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\
    ^hash_code sm = (op,sb) /\ ^hash_code shadow_sm = (op,shadow_sb) /\
    gas_shadow_state sm shadow_sm /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func /\
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
      ^child_post
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac hash_operand_shape >>
  qpat_x_assum `args = [_]` SUBST_ALL_TAC >>
  qpat_x_assum `ann = BaseT _` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac hash_compiler_cuts >>
  drule_all_then assume_tac hash_prefix_admissible >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `!DF lo d PG src tops ctx sh fn sfn ce en ty es. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (mp_tac o SRULE [IMP_CONJ_THM,FORALL_AND_THM]) >>
     disch_then (irule o CONJUNCT1) >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  qexistsl_tac [`e`,`x`,`sm`,`shadow_sm`,`op`] >> simp[] >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ _ _` (irule o REWRITE_RULE [expr_sim_full_mods_def]) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  qexistsl_tac [`shadow_sa`,`shadow_sm`] >> simp[]
QED
