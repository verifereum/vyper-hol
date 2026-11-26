(* Composition at the reached uint256 operand of BlockHash and BlobHash. *)
Theory bodyIndexedHashComposeMods
Ancestors vyperValue[qualified,ignore_grammar]
  bodyFullPredsMods bodyForRangeScalarFrameMods bodyFullShared bodySimStmtFacts
  bodyFullHashKeccakFixed[qualified] bodyFullGhostFrame exprBodyPreProps
  exprWordOperand exprSimBuiltins exprSimUnopComposeProps exprSimWordArgs
  gasShadowCompileStmtHelpers gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods vyperStorageTrace vyperTypeBuiltins exprSimOperands
  builtinProps emitHelperProps vyperStorageFootprint vyperTypeSystem
  loweringPosts exprSimMemDefs stmtSimProps externalEntryShape
  exprSimHypsDefs allocLimits supportedExprTraverse vyperTypeCallGraph
  vyperExprEffects vyperAST vyperState vyperContext vyperInterpreter
  exprLowering exprLoweringProps compileEnv bodyFullPostsMods bodyFullShadowBodyInv
  bodyPtrDefs venomState bodyInvSplit fragExec gasSummary gasContext
  integer arithmetic exprSimDefs exprSimAccounts bodyWriteSubscriptSourceMods
  bodyFullUnwrapRun exprSimProps freshWrites
Libs intLib

val hashindex = ``BaseT (UintT 256)``;
val hashresult = ``BaseT (BytesT (Fixed 32))``;
val hashcode = ``\bt x. if bt = vyperAST$BlockHash then compile_blockhash x else emit_op BLOBHASH [x]``;
val hash_tail = ``\v ee. (unop_result cx ^hashresult bt [^hashindex] v ee,ee)``;

fun suffix bt emit need_fresh =
 ``!arg sa op sb func st0 cenv cx mid s ctx DF lo G tn explicit PG i.
    ^emit arg sa = (op,sb) /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ storage_trace_domain cx st0 mid.storage_trace /\
    local_ptrs_reserved cenv sa /\ 0 <= i /\ i < 2 ** 256 /\
    eval_operand arg s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
    op_taint tn arg = {} /\ op_prov G arg = NONE /\ ^need_fresh /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
    allocas_from lo s /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func cenv cx mid s) ==>
    ?r G' tn'. !H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
      case unop_result cx ^hashresult ^bt [^hashindex] (IntV i) mid of
        INL v => ?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) /\
          expr_val_rel cx ^hashresult v op t /\ op_taint tn' op = {} /\ op_prov G' op = NONE /\
          stmt_state_rel H ctx func cenv cx mid t /\ alloca_history func t /\
          tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
          tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
          (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
               FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p))
      | INR ex => (?u. r = Abort Revert_abort u) /\ expr_exit (INR ex) r /\
                  halt_exit H cx mid (INR ex) r``;

val sblock = suffix ``vyperAST$BlockHash`` ``compile_blockhash``
  ``!p. arg = Var p ==> not_fresh_at sa p``;
val sblob = suffix ``vyperAST$BlobHash`` ``\arg. emit_op BLOBHASH [arg]`` ``T``
  |> (fn t => rhs (concl (SIMP_CONV bool_ss [] t)));

Theorem indexed_hash_inputs[local]:
  (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
  expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
  ?e. args = [e] /\ a = ^hashresult /\ expr_type e = ^hashindex
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  Cases_on `bt = vyperAST$BlockHash` >> gvs[] >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[] >> rename1 `h::t` >> Cases_on `t` >> simp[]
QED

Theorem indexed_hash_operand_pre[local]:
  (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
  expr_body_pre_mods mods cenv cx env (Builtin a bt [e]) es ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  strip_tac >> Cases_on `bt = vyperAST$BlockHash` >> gvs[] >>
  fs[expr_body_pre_mods_def, Once well_typed_expr_def,
     well_typed_builtin_app_def, byte_widths_expr_def, alloc_limits_expr_def,
     constSubstCorrectTheory.frame_well_typed_exprs_every,
     int_calls_expr_def, expr_has_evm_run_thm, supported_expr_exists_def]
QED

Theorem indexed_hash_child[local]:
  body_exprs_full_ok_mods mods exps cx [e] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (first_x_assum irule >> simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >> qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem indexed_hash_code_cut[local]:
  (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
  lower_value compile_expr cenv ty (Builtin ann bt [e]) sa = (op,sb) ==>
  ?x sm. lower_value compile_expr cenv ty e sa = (x,sm) /\
    ^hashcode bt x sm = (op,sb)
Proof
  strip_tac >> Cases_on `bt = vyperAST$BlockHash` >> gvs[]
  >- (drule lower_value_blockhash >> simp[]) >>
  drule lower_value_blobhash >> simp[]
QED

Theorem indexed_hash_suffix_extends[local]:
  (bt = vyperAST$BlockHash \/ bt = BlobHash) /\ ^hashcode bt x sa = (op,sb) ==> cs_extends sa sb
Proof
  strip_tac >> Cases_on `bt = vyperAST$BlockHash` >> gvs[]
  >- (mp_tac (Q.SPECL [`x`,`sa`,`K T`] compile_blockhash_labels) >> simp[]) >>
  drule emit_op_extends_next_var >> simp[]
QED

Theorem indexed_hash_paired_prefix[local]:
  (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
  lower_value compile_expr cenv ty (Builtin ann bt [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin ann bt [e])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x sm shsm.
    lower_value compile_expr cenv ty e sa = (x,sm) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr e) shadow_sa = (x,shsm) /\
    ^hashcode bt x sm = (op,sb) /\
    gas_shadow_state sm shsm /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shsm shadow_func /\ sa.cs_next_var <= sm.cs_next_var
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac indexed_hash_code_cut >>
  `?sx shsm. lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr e) shadow_sa = (sx,shsm) /\ ^hashcode bt sx shsm = (op,shadow_sb)` by
    (irule indexed_hash_code_cut >> simp[] >> qexists_tac `ann` >>
     Cases_on `bt = vyperAST$BlockHash` >> gvs[gasShadowTheory.gas_shadow_expr_def,
                                      gasShadowTheory.gas_shadow_builtin_def]) >>
  `sx = x /\ gas_shadow_state sm shsm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ e sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
     simp[] >> irule gas_shadow_stmt_lower_value_env) >>
  qexistsl_tac [`x`,`sm`,`shsm`] >> simp[] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var` by
    (qspecl_then [`cenv`,`ty`,`e`,`sa`] mp_tac ci_mono_lower_value_compile_expr >> simp[ci_mono_def]) >>
  `cs_extends shadow_sa shsm` by
    (qspecl_then [`gas_shadow_env T cenv`,`ty`,`gas_shadow_expr e`,`shadow_sa`]
      mp_tac ci_mono_lower_value_compile_expr >> simp[ci_mono_def]) >>
  `cs_extends sm sb` by (irule indexed_hash_suffix_extends >> goal_assum (drule_at Any) >> simp[]) >>
  `cs_extends shsm shadow_sb` by (irule indexed_hash_suffix_extends >> goal_assum (drule_at Any) >> fs[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by (irule fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shsm shadow_func /\ fn_has_code shsm shadow_sb shadow_func` by
    (irule fn_has_code_split >> simp[]) >> simp[]
QED

Theorem indexed_hash_bind[local]:
  (bt = vyperAST$BlockHash \/ bt = BlobHash) /\ expr_type e = ^hashindex /\
  (!H res ee gt r. R H res ee gt r ==> ?exc. res = INR exc) /\
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) Qchild R /\
  (!marks res mid G tn t.
    (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (res,mid with gas_obs := tail)) /\ storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      Qchild H res mid G tn t /\ mid.gas_obs = [] /\ ~t.vs_halted) ==>
    ?v. res = INL v /\
      gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
        (^hash_tail v) (mid,t,G,tn) Q R) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx (Builtin ^hashresult bt [e])) (read_result cx))
    (es,s0,G0,tn0) Q R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx (Builtin ^hashresult bt [e])) (read_result cx) =
   bind (bind (eval_expr cx e) (read_result cx)) ^hash_tail` by
    (dep_rewrite.DEP_REWRITE_TAC[eval_expr_unop_action_general] >>
     Cases_on `bt = vyperAST$BlockHash` >>
     gvs[builtin_args_length_ok_def, precompile_builtin_def,is_self_codesize_def]) >>
  pop_assum SUBST1_TAC >> irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >- simp[storage_trace_frame_def,exprSimUnopPropsTheory.unop_result_def] >>
  qexists_tac `\H res ee G tn t. Qchild H res ee G tn t /\ ee.gas_obs = [] /\ ~t.vs_halted` >>
  BETA_TAC >> conj_tac
  >- (rpt strip_tac >> disj1_tac >>
      qpat_assum `!marks res mid G tn t. _` (irule o BETA_RULE) >>
      conj_tac >- (qexists_tac `marks` >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem indexed_hash_child_type[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = ^hashindex /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,mid) ==>
  ?i. v = IntV i /\ 0 <= i /\ i < 2 ** 256
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by
    simp[write_subscript_source_gas_obs_mods] >>
  `value_runtime_typed env (expr_type e) v` by
    (qpat_assum `bind (eval_expr cx e) _ _ = (INL v,mid)`
       (mp_then Any mp_tac (SIMP_RULE (srw_ss()) [SF ETA_ss] expr_body_pre_eval_mods)) >>
     disch_then (qspecl_then [`mods`,`env`,`cenv`] mp_tac) >> simp[]) >>
  qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,vyperValueTheory.evaluate_type_def] >>
  Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def] >> intLib.COOPER_TAC
QED

Theorem indexed_hash_operand_fresh[local]:
  expr_body_pre_mods mods cenv cx env e es /\ expr_type e = ^hashindex /\
  lower_value compile_expr cenv ty e sa = (x,sm) ==>
  !p. x = Var p ==> not_fresh_at sm p
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (rpt strip_tac >> drule_all exprSimSourceTheory.env_consistent_var_type_evaluates >>
     simp[vyperTypeSystemTheory.well_formed_type_def]) >>
  `is_word_type (expr_type e)` by simp[is_word_type_def] >>
  drule_all lower_value_word_shape >> simp[]
QED

val hash_q = ``\H res ee G tn t. ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx (Builtin ^hashresult bt [e]) es sa sb s0 ee v op t /\
  expr_store_bound cx ^hashresult v op t /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\ ptr_val_ok cx ^hashresult v op G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val hash_r = ``\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;

Theorem indexed_hash_normal_post[local]:
  (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 mid v x s /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G tn s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) /\
  (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s /\
       FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  stmt_state_rel H ctx func cenv cx mid t /\ alloca_history func t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  expr_val_rel cx ^hashresult w op t /\ op_taint tn' op = {} /\ op_prov G' op = NONE ==>
  ^hash_q H (INL w) mid G' tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> BETA_TAC >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` (strip_assume_tac o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ e _ _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `immutable_frame_mods func cenv cx mid t` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl_tac [`mid`,`s`,`sm`] >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' t` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G`,`mid`,`s`,`sm`,`tn`] >> simp[]) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
       FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >>
     `not_fresh_at sm p` by metis_tac[freshWritesTheory.not_fresh_at_mono] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >> qexistsl_tac [`G`,`tn`] >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `stmt_state_rel H _ _ _ _ mid t`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  simp[expr_store_bound_word,ptr_val_ok_def,is_word_type_def] >>
  simp[expr_post_mods_def,expr_post_def,expr_type_def,is_word_type_def,expr_val_at_def] >>
  `locals_kept cenv es mid s0 t` by (irule locals_kept_mem_tail >> qexists_tac `s` >> simp[]) >>
  `expr_has_effect (Builtin ^hashresult bt [e]) = expr_has_effect e` by
    (Cases_on `bt = vyperAST$BlockHash` >> gvs[expr_has_effect_def]) >>
  `~expr_has_effect e ==> pure_frame cenv func es sa s0 t` by
    (disch_tac >> irule pure_frame_mem_tail >> qexists_tac `s` >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem indexed_hash_value[local]:
  ^sblock /\ ^sblob /\ (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
  expr_type e = ^hashindex /\ expr_body_pre_mods mods cenv cx env e es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Builtin ^hashresult bt [e]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac indexed_hash_paired_prefix >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (irule unop_operand_admissible >> qexistsl_tac [`^hashresult`,`bt`] >>
     Cases_on `bt = vyperAST$BlockHash` >>
     gvs[builtin_args_length_ok_def,precompile_builtin_def,is_self_codesize_def]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[not_fresh_at_mono] >>
  `!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p` by
    metis_tac[not_fresh_at_mono] >>
  `!p. x = Var p ==> not_fresh_at sm p` by
    (match_mp_tac indexed_hash_operand_fresh >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shsm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule indexed_hash_bind >> qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[post_value_type_word,expr_type_def,is_word_type_def] >> conj_tac
  >- (rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def,expr_exit_INR_type]) >>
  suspend "reached"
QED

Resume indexed_hash_value[reached]:
  qx_genl_tac [`marks`,`res`,`mid`,`G`,`tn`,`s`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _` (drule_then strip_assume_tac) >>
  qexists_tac `v` >> simp[] >> qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` (mp_tac o SIMP_RULE (srw_ss()) [])) >> asm_rewrite_tac[]) >>
  drule_all_then strip_assume_tac indexed_hash_child_type >>
  qpat_x_assum `v = IntV i` SUBST_ALL_TAC >>
  `allocas_from lo s` by fs[ghost_inv_at_mods_def] >>
  `eval_operand x s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) (IntV i)) /\
   op_taint tn x = {} /\ op_prov G x = NONE` by
    (fs[expr_post_mods_def,expr_post_def,expr_val_rel_def,ptr_val_ok_def,
       post_value_type_word,is_word_type_def,vyperValueTheory.evaluate_type_def] >> (gvs[expr_post_mods_def, expr_post_def, expr_val_rel_def, ptr_val_ok_def, post_value_type_word, is_word_type_def, vyperValueTheory.evaluate_type_def])) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> stmt_state_rel H ctx func cenv cx mid s` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
      (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  suspend "suffix"
QED

Resume indexed_hash_value[suffix]:
  `?r G' tn'. !H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (s,G,tn) [] (r,G',tn') /\
      case unop_result cx ^hashresult bt [^hashindex] (IntV i) mid of
        INL w => ?t. r = OK t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          t = (s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>) /\
          expr_val_rel cx ^hashresult w op t /\ op_taint tn' op = {} /\ op_prov G' op = NONE /\
          stmt_state_rel H ctx func cenv cx mid t /\ alloca_history func t /\
          tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
          tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
          (!p. not_fresh_at sm p ==> lookup_var p t = lookup_var p s /\
               FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p))
      | INR ex => (?u. r = Abort Revert_abort u) /\ expr_exit (INR ex) r /\
                  halt_exit H cx mid (INR ex) r` by
    (Cases_on `bt = vyperAST$BlockHash` >> gvs[]
     >- (qpat_assum `!arg sa op sb func st0 cenv cx mid s ctx DF lo G tn explicit PG i.
            compile_blockhash arg sa = _ /\ _ ==> _` irule >>
         simp[expr_post_mods_def,expr_post_def] >> qexists_tac `x` >> simp[]) >>
     qpat_assum `!arg sa op sb func st0 cenv cx mid s ctx DF lo G tn explicit PG i.
            emit_op BLOBHASH [arg] sa = _ /\ _ ==> _` irule >>
     simp[expr_post_mods_def,expr_post_def] >> qexists_tac `x` >> simp[]) >>
  Cases_on `unop_result cx ^hashresult bt [^hashindex] (IntV i) mid`
  >- suspend "normal" >> suspend "exit"
QED

Resume indexed_hash_value[normal]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `unop_result _ _ _ _ _ mid = _` (fn eq =>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  qpat_x_assum `r = OK t` SUBST_ALL_TAC >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL x'`,`t`,`tn'`] >>
  conj_tac >- (gen_tac >> qpat_assum `unop_result _ _ _ _ _ mid = _` (mp_tac o REWRITE_RULE [exprSimUnopPropsTheory.unop_result_def]) >>
    simp[exprSimUnopPropsTheory.unop_result_def]) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `unop_result _ _ _ _ _ mid = _` (fn eq =>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> (?v. _ ) /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `unop_result _ _ _ _ _ mid = _` (fn eq =>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  qpat_assum `mid with gas_obs := [] = mid` (fn eq => pure_rewrite_tac [eq]) >>
  irule (BETA_RULE indexed_hash_normal_post) >>
  simp[] >> qexistsl_tac [`G`,`s`,`sm`,`tn`,`IntV i`,`x`] >> simp[] >>
  qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts` (fn idx =>
    qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>`
      (ACCEPT_TAC o REWRITE_RULE [idx]))
QED

Resume indexed_hash_value[exit]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `unop_result _ _ _ _ _ mid = _` (fn eq =>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  qpat_x_assum `r = Abort Revert_abort u` SUBST_ALL_TAC >>
  irule gas_outcome_full_mods_exit_revert >> simp[] >>
  qexistsl_tac [`G'`,`mid`,`INR y`,`tn'`,`u`] >>
  simp[exit_result_def] >>
  conj_tac >- (gen_tac >> qpat_assum `unop_result _ _ _ _ _ mid = _`
      (mp_tac o REWRITE_RULE [exprSimUnopPropsTheory.unop_result_def]) >>
    simp[exprSimUnopPropsTheory.unop_result_def]) >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `unop_result _ _ _ _ _ mid = _` (fn eq =>
    disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])) >>
  conj_tac
  >- (qpat_assum `expr_exit (INR y) (Abort Revert_abort u)` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[expr_exit_INR_type]) >>
  qpat_assum `halt_exit H cx mid (INR y) (Abort Revert_abort u)`
    (mp_tac o REWRITE_RULE [halt_exit_def]) >>
  simp[halt_exit_def]
QED

Finalise indexed_hash_value

Theorem indexed_hash_read_from_suffixes_mods:
  ^sblock /\ ^sblob ==>
  (!DF lo d ctx sh PG f sf cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
    (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es) ==>
  !exps src tops DF lo d ctx shadow_ctx PG func shadow_func cenv env cx ty a bt args es.
    (bt = vyperAST$BlockHash \/ bt = BlobHash) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin a bt args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac indexed_hash_inputs >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  qpat_x_assum `a = ^hashresult` SUBST_ALL_TAC >>
  `body_exprs_full_ok_mods mods exps cx [e]` by
    (Cases_on `bt = vyperAST$BlockHash` >> gvs[builtin_args_length_ok_def]) >>
  `expr_body_pre_mods mods cenv cx env e es` by
    (irule indexed_hash_operand_pre >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (irule indexed_hash_child >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  conj_asm1_tac
  >- (irule indexed_hash_value >>
      ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
      simp[] >> qexistsl_tac [`env`,`mods`] >> simp[]) >>
  qpat_assum `!DF lo d ctx sh PG f sf cenv cx ty e es. _ ==> expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
  simp[expr_type_def,is_word_type_def] >> conj_tac
  >- (Cases_on `bt = vyperAST$BlockHash` >> gvs[compile_blockhash_stack,compile_blobhash_stack]) >>
  rpt strip_tac >> drule eval_expr_builtin_value >> simp[]
QED
