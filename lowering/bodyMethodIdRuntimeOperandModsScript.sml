(* MethodId evaluates and forces exactly one child before hashing it. *)
Theory bodyMethodIdRuntimeOperandMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShared bodyInvCodeProps
  exprBodyPreProps exprBodyPreTypingProps exprSimHash exprSimSource
  exprSimUnopComposeProps exprSimUnopProps exprSimHypsDefs exprSimWordArgs exprSimStack
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods gasStorage gasShadowCompileStmtHelpers gasShadowCompilePure gasShadowState
  gasShadow gasContext exprLoweringProps exprLowering loweringPosts
  bodyPtrDefs exprSimDefs stmtSimProps haltExitProj
  vyperStorageTrace vyperStorageFootprint vyperTypeSystem vyperTypeBuiltins
  vyperTypeCallGraph vyperAST vyperState vyperInterpreter
  supportedExprTraverse allocLimits compileEnv fragExec context list vyperContext
  builtinHashing builtinSimple
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
Libs monadsyntax

Theorem method_id_child_pre_mods[local]:
  expr_body_pre_mods mods cenv cx env (Builtin ann MethodId [e]) es ==>
  expr_body_pre_mods mods cenv cx env e es /\
  is_bytes_or_string_type (expr_type e) /\
  (ann = BaseT (BytesT (Dynamic 4)) \/ ann = BaseT (BytesT (Fixed 4)))
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       int_calls_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM] >>
  strip_tac >> fs[Once well_typed_expr_def] >>
  mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `ann`, `ts` |-> `[expr_type e]`]
    hash_builtin_types) >> simp[]
QED

Theorem method_id_child_value_mods[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!a b c d e f g h i j k l m n. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (drule_all_then (mp_tac o SPEC_ALL)) >> simp[]
QED

Theorem method_id_source[local]:
  eval_expr cx (Builtin ann MethodId [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
               INL r => INL (Value r) | INR ex => INR ex),mid))
Proof
  irule eval_expr_unary_builtin_action >>
  simp[builtin_args_length_ok_def,is_self_codesize_def]
QED

Theorem method_id_forced_source[local]:
  bind (eval_expr cx (Builtin ann MethodId [e])) (read_result cx) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
               INL r => INL r | INR ex => INR ex),mid))
Proof
  mp_tac (Q.INST [`bi` |-> `MethodId`, `ann` |-> `ann`, `e` |-> `e`, `cx` |-> `cx`]
    eval_expr_unop_action_general) >>
  simp[builtin_args_length_ok_def, is_self_codesize_def, builtin_result_def,
       unop_result_def, precompile_builtin_def] >>
  disch_then SUBST1_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
  rpt gen_tac >> CASE_TAC >> simp[]
QED

Theorem method_id_admissible_child[local]:
  gas_admissible (bind src next) expr_res_ok es ==>
  gas_admissible (src : evaluation_state -> value evaluation_result) expr_res_ok es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum irule >> qexistsl_tac [`ee`,`gs`] >> simp[bind_def]
QED

Theorem method_id_child_post_type[local]:
  expr_body_pre_mods mods cenv cx env e es /\ is_bytes_or_string_type (expr_type e) ==>
  post_value_type cenv e = expr_type e
Proof
  strip_tac >>
  Cases_on `?a fid args drv. e = Call a (IntCall fid) args drv`
  >- (gvs[] >> PairCases_on `fid` >>
      drule_then assume_tac expr_body_pre_mods_inv >>
      drule_then assume_tac expr_body_pre_mods_well_typed >>
      fs[Once well_typed_expr_def, expr_type_def] >>
      drule_all_then assume_tac expr_sim_inv_mods_return_type >>
      simp[post_value_type_def, lowered_value_type_def, expr_type_def] >>
      Cases_on `a` >> gvs[] >> rename1 `is_bytes_or_string_type (BaseT bt)` >>
      Cases_on `bt` >> gvs[is_bytestring_type_def, type_widens_to_def, arg_type_fits_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[is_bytestring_type_def, is_word_type_def, arg_type_fits_def,
          well_formed_type_def, vyperValueTheory.evaluate_type_def,
          optionTheory.IF_EQUALS_OPTION]) >>
  irule post_value_type_not_int_call >>
  qpat_x_assum `~(?a fid args drv. _)` mp_tac >> simp[]
QED

val method_arg_post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx e es sa sm s0 mid v x t /\
  expr_store_bound cx (expr_type e) v x t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d cenv cx mid G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val method_expr = ``Builtin ann MethodId [e]``;
val method_vv = ``if fixed then StackValue ann op else LocatedValue ann (mk_ptr op LocMemory)``;
val method_value_post = ``
  expr_post_mods (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx ^method_expr es sa sb s0 mid r op z /\
  expr_store_bound cx ann r op z /\
  z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func z /\
  s0.vs_alloca_next <= z.vs_alloca_next /\ ghost_inv_at_mods (DF (H : (bool # 256 word # type_value) list # num list)) lo d cenv cx mid G' tn' z /\
  ptr_val_ok cx ann r op G' tn' z /\ (~fixed ==> ptr_buf_ok cenv ^method_expr op G' z) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'``;
val method_vv_post = ``
  vv_post_mods (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx ^method_expr es sa sb s0 mid (Value r) ^method_vv z /\
  vv_store_bound cx ann (lowered_value_type cenv ^method_expr) mid (Value r) ^method_vv z /\
  ptr_vv_ok cx ann (Value r) ^method_vv mid G' tn' z``;
val method_tail = ``\v (mid:evaluation_state).
  ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
    INL r => INL ((encode:value -> 'a) r) | INR ex => INR ex),mid)``;
val method_suffix = ``
  !DF lo d explicit ctx func PG exps src tops cenv cx env ann e es sa sm sb s0 st0
     mid v x t G0 tn0 G tn fixed op.
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    expr_body_pre_mods mods cenv cx env ^method_expr es /\
    ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    (!H. dead_lo_ok_mods (H : (bool # 256 word # type_value) list # num list) (DF H) lo cenv cx) /\ local_ptrs_reserved cenv sa /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    return_buf_frame d cenv sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
    (?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    mid.gas_obs = [] /\ ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> ^method_arg_post) ==>
    ?r z G' tn'.
      builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
      (!H. valid_horizon cx st0 H mid.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G',tn') /\
        ^method_value_post /\ ^method_vv_post)``;

Theorem method_runtime_cuts[local]:
  method_id_literal e = NONE /\
  ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  (lower_value compile_expr cenv ty ^method_expr sa = (op,sb) /\
   lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^method_expr) sha = (op,shb) \/
   compile_expr cenv ty ^method_expr sa = (^method_vv,sb) /\
   compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^method_expr) sha = (^method_vv,shb)) ==>
  ?x sm shm.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha = (x,shm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm func /\ fn_has_code sha shm shadow_func
Proof
  strip_tac >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ e sa = (x,sm)` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) sha` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) sha = (sx,shm)` >>
  `sx = x /\ gas_shadow_state sm shm` by
    (irule gas_shadow_step >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[gas_shadow_stmt_lower_value_env]) >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  Cases_on `compile_method_id_runtime (expr_type e) x fixed sm` >>
  Cases_on `compile_method_id_runtime (expr_type e) x fixed shm` >>
  rename1 `compile_method_id_runtime _ _ _ sm = (oq,sc)` >>
  rename1 `compile_method_id_runtime _ _ _ shm = (osq,shc)` >>
  `compile_expr cenv ty ^method_expr sa =
       ((if fixed then StackValue ann oq else LocatedValue ann (mk_ptr oq LocMemory)),sc)` by
    (Cases_on `fixed` >> gvs[compile_method_id_singleton_runtime,as_stack_val_def,
                            as_ptr_val_def,comp_bind_def,comp_return_def]) >>
  `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr ^method_expr) sha =
       ((if fixed then StackValue ann osq else LocatedValue ann (mk_ptr osq LocMemory)),shc)` by
    (Cases_on `fixed` >> gvs[gas_shadow_expr_def,gas_shadow_builtin_def,
       compile_method_id_singleton_runtime,gas_shadow_expr_type,as_stack_val_def,
       as_ptr_val_def,comp_bind_def,comp_return_def]) >>
  `oq = op /\ sc = sb /\ shc = shb` by
    (Cases_on `fixed` >>
     gvs[lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def,
         is_word_type_def,mk_ptr_def]) >>
  gvs[] >>
  `cs_appends (compile_method_id_runtime (expr_type e) x fixed)` by simp[cj 5 hash_suffix_appends] >>
  simp[] >> metis_tac[fn_has_code_split,cj 2 compile_expr_grows,cs_appends_def]
QED

val method_exit = ``\(H:(bool # 256 word # type_value) list # num list) (res:'a + vyperState$exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

Theorem method_id_bind_mods[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Qchild
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) /\
  (!marks res mid G tn t.
     (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (res,mid with gas_obs := tail)) /\ storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Qchild H res mid G tn t /\ mid.gas_obs = [] /\ ~t.vs_halted) ==>
     ?v. res = INL v /\
         gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
           ((^method_tail) v) (mid,t,G,tn) Q ^method_exit) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) ^method_tail)
    (es,s0,G0,tn0) Q ^method_exit
Proof
  strip_tac >> irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >- simp[storage_trace_frame_def] >>
  qexists_tac `\H res mid G tn t. Qchild H res mid G tn t /\ mid.gas_obs = [] /\ ~t.vs_halted` >>
  BETA_TAC >> conj_tac
  >- (rpt strip_tac >> disj1_tac >>
      qpat_x_assum `!marks res mid G tn t. _` (drule_all_then (ACCEPT_TAC o BETA_RULE))) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> qx_gen_tac `H` >> Cases >> simp[expr_exit_def] >>
  ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
                    INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]
QED

Theorem method_tail_pure[local]:
  builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
  mid.gas_obs = [] /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G',tn') /\
    Q H (INL (encode r)) mid G' tn' z) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    ((^method_tail) v) (mid,t,G,tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL (encode r)`,`z`,`tn'`] >>
  simp[evaluation_state_component_equality] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >> simp[]
QED

val method_stage = ``
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  expr_body_pre_mods mods cenv cx env ^method_expr es /\
  ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok_mods (H : (bool # 256 word # type_value) list # num list) (DF H) lo cenv cx) /\ local_ptrs_reserved cenv sa /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  return_buf_frame d cenv sa s0``;
val method_q = ``\H (res:'a + vyperState$exception) mid G' tn' z. ?r. res = INL ((encode:value -> 'a) r) /\
  ^method_value_post /\ ^method_vv_post``;

Theorem method_join_suffix_mods[local]:
  ^method_suffix /\ ^method_stage /\
  post_value_type cenv e = expr_type e /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res mid G tn t. ?v. res = INL v /\ ^method_arg_post /\
       t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) ^method_tail)
    (es,s0,G0,tn0) ^method_q ^method_exit
Proof
  strip_tac >> irule method_id_bind_mods >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qexists_tac `v` >> simp[] >>
  `?xs. !tail. bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs ++ tail) =
    (INL v, mid with gas_obs := tail)` by
    (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> ^method_arg_post` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >> gvs[]) >>
  `?r z G' tn'.
     builtin_result cx mid.accounts ann MethodId [expr_type e] [v] = INL r /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G',tn') /\
       ^method_value_post /\ ^method_vv_post)` by
    (qpat_assum `!DF lo d explicit ctx func PG exps src tops cenv cx env ann e es sa sm sb s0 st0
        mid v x t G0 tn0 G tn fixed op. _` irule >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (qexists_tac `xs` >> first_assum ACCEPT_TAC)
     >- (qexistsl_tac [`sm`,`x`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     goal_assum (drule_at Any) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule (BETA_RULE method_tail_pure) >>
  simp[] >> qexistsl_tac [`G'`,`r`,`tn'`,`z`] >> BETA_TAC >> simp[] >>
  reverse conj_tac >- (Cases_on `fixed` >> gvs[]) >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> qexists_tac `r` >> Cases_on `fixed` >> gvs[]
QED

Theorem method_runtime_child_run_mods[local]:
  ^method_suffix /\ ^method_stage /\ method_id_literal e = NONE /\
  post_value_type cenv e = expr_type e /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa = (x,shm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sm func /\
  fn_has_code shadow_sa shm shadow_func /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) ^method_tail)
    (es,s0,G0,tn0) ^method_q ^method_exit
Proof
  strip_tac >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`x`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule method_join_suffix_mods >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`sm`,`x`] >> asm_rewrite_tac[] >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  BETA_TAC >> simp[] >> rpt strip_tac >> qexists_tac `v` >> fs[]
QED

Theorem method_runtime_vv_shape[local]:
  method_id_literal e = NONE /\
  ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)) /\
  compile_expr cenv ty ^method_expr sa = (vv,sb) ==>
  ?op. vv = ^method_vv
Proof
  strip_tac >> Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value _ _ _ e sa = (x,sm)` >>
  Cases_on `compile_method_id_runtime (expr_type e) x fixed sm` >>
  Cases_on `fixed` >>
  gvs[compile_method_id_singleton_runtime,as_stack_val_def,as_ptr_val_def,comp_bind_def,comp_return_def,
      mk_ptr_def]
QED

Theorem method_id_runtime_from_suffix_mods:
  ^method_suffix ==>
  !exps src tops DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty ann e es.
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann MethodId [e]) es /\
    body_expr_full_ok_mods mods exps cx e /\ method_id_literal e = NONE ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann MethodId [e]) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann MethodId [e]) es
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `expr_body_pre_mods mods cenv cx env e es /\ is_bytes_or_string_type (expr_type e) /\
   ?fixed. ann = BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))` by
    (drule_then strip_assume_tac method_id_child_pre_mods
     >- (simp[] >> qexists_tac `F` >> simp[]) >> simp[] >> qexists_tac `T` >> simp[]) >>
  `post_value_type cenv e = expr_type e` by (irule method_id_child_post_type >> metis_tac[]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e es` by
    (irule method_id_child_value_mods >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  conj_tac >- suspend "forced" >> suspend "vv"
QED

Resume method_id_runtime_from_suffix_mods[forced]:
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `?x sm shm.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (x,shm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm func /\ fn_has_code shadow_sa shm shadow_func` by
    (irule method_runtime_cuts >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexistsl_tac [`ann`,`shadow_sb`,`ty`] >> asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (qpat_assum `gas_admissible (bind (eval_expr _ (Builtin _ MethodId _)) _) _ _`
       (mp_tac o REWRITE_RULE [method_id_forced_source]) >>
     MATCH_ACCEPT_TAC method_id_admissible_child) >>
  qpat_x_assum `gas_admissible (bind (eval_expr _ (Builtin _ MethodId _)) _) _ _` kall_tac >>
  PURE_REWRITE_TAC[method_id_forced_source] >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any (BETA_RULE (Q.INST [`encode` |-> `\v:value. v`]
    (INST_TYPE [alpha |-> ``:value``] method_runtime_child_run_mods))) >>
  BETA_TAC >> suspend "forced_post"
QED

Resume method_id_runtime_from_suffix_mods[vv]:
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `?op. vv = ^method_vv` by
    (irule method_runtime_vv_shape >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexistsl_tac [`cenv`,`e`,`sa`,`sb`,`ty`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `?x sm shm.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa = (x,shm) /\
    compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm func /\ fn_has_code shadow_sa shm shadow_func` by
    (irule method_runtime_cuts >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
     qexistsl_tac [`ann`,`shadow_sb`,`ty`] >> asm_rewrite_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule method_id_admissible_child >>
     qexists_tac `\v mid. ((case builtin_result cx mid.accounts ann MethodId [expr_type e] [v] of
                          INL r => INL r | INR ex => INR ex),mid)` >>
     rewrite_tac[GSYM method_id_forced_source] >>
     irule eval_expr_force_admissible >> conj_tac
     >- (rpt strip_tac >> drule eval_expr_builtin_value >> simp[])
     >> asm_rewrite_tac[]) >>
  PURE_REWRITE_TAC[method_id_source] >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any (BETA_RULE (Q.INST [`encode` |-> `Value`]
    (INST_TYPE [alpha |-> ``:eval_result``] method_runtime_child_run_mods))) >>
  BETA_TAC >> suspend "vv_post"
QED

Resume method_id_runtime_from_suffix_mods[forced_post]:
  qexistsl_tac [`x`,`tops`,`src`,`sm`,`shm`,`shadow_sa`,`shadow_func`,
                 `sb`,`sa`,`op`,`mods`,`fixed`,`exps`,`env`,`d`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  simp[] >> rpt strip_tac >> qexists_tac `r` >>
  Cases_on `fixed` >> gvs[expr_type_def,is_word_type_def] >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)
    expr_post_state >> simp[]
QED

Resume method_id_runtime_from_suffix_mods[vv_post]:
  qexistsl_tac [`x`,`tops`,`src`,`sm`,`shm`,`shadow_sa`,`shadow_func`,
                 `sb`,`sa`,`op`,`mods`,`fixed`,`exps`,`env`,`d`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  simp[] >> rpt strip_tac >> qexists_tac `Value r` >>
  Cases_on `fixed` >> gvs[expr_type_def,is_word_type_def,is_bytestring_type_def,
                        vv_location_def,mk_ptr_def] >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)
    expr_post_state >> simp[]
QED

Finalise method_id_runtime_from_suffix_mods
