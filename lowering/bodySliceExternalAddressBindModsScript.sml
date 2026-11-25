(* Bind the reached external Slice address read to its VV continuation. *)
Theory bodySliceExternalAddressBindMods
Ancestors
  bodyReachedWordResultBindMods bodySliceWordEntryMods bodyWriteSubscriptSourceMods
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach exprSimFullBundleProps
  exprLoweringProps exprSimHypsDefs vyperStorageTrace vyperStorageFootprint
  vyperState compileEnv loweringPosts exprSimPrecompiles exprWordOperand
Libs monadsyntax

val wp = ``\e es sa sb s0 ee v op t G0 tn0 G tn
    (H:(bool # 256 word # type_value) list # num list).
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  ~t.vs_halted /\ ee.gas_obs = [] /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val cut = ``\e es sa sb s0 ee v op t G0 tn0 G tn marks.
  (!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> ^wp e es sa sb s0 ee v op t G0 tn0 G tn H)``;

val entry = ``\es sa s0 G0 tn0.
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;
val child = ``\ty e sa sb sha shb op.
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  sa.cs_next_var <= sb.cs_next_var``;
val outcome = ``\(source : evaluation_state -> eval_result evaluation_result).
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 source``;
val exit_weaken = ``!(H : (bool # 256 word # type_value) list # num list)
  (res : eval_result + vyperState$exception) ee
  (gt : (string |-> num # num) # taint) r. expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u) ==> R H res ee gt r``;

Theorem slice_external_address_bind_mods:
  body_exprs_full_ok_mods mods exps cx [addr] /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env fin /\
  expr_body_pre_mods mods cenv cx env addr fin /\
  expr_type addr = BaseT AddressT /\
  ^child ty addr s2 s3 sh2 sh3 aop /\ ^entry fin s2 t2 G2 tn2 /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  gas_admissible (bind (^forced addr) next) expr_vv_res_ok fin /\
  (!v. storage_trace_frame (next v)) /\ ^exit_weaken /\
  (!marks bs ae G3 tn3 z.
    ^cut addr fin s2 s3 t2 ae (BytesV bs) aop z G2 tn2 G3 tn3 marks /\
    LENGTH bs = 20 /\
    eval_operand aop z = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
    op_prov G3 aop = NONE /\ op_taint tn3 aop = {} /\
    (!q. aop = Var q ==> not_fresh_at s3 q) /\
    (!l. aop <> Label l) /\ ^entry ae s3 z G3 tn3 /\
    expr_sim_inv_mods mods cenv cx env ae /\
    body_const_cells_agree_mods mods cx env ae /\
    gas_admissible (next (BytesV bs)) expr_vv_res_ok ae ==>
    ^outcome (next (BytesV bs)) (ae,z,G3,tn3) Q R) ==>
  ^outcome (bind (^forced addr) next) (fin,t2,G2,tn2) Q R
Proof
  BETA_TAC >> strip_tac >>
  qpat_x_assum `body_exprs_full_ok_mods _ _ _ [_]`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ addr`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty addr fin /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty addr fin` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     fs[expr_sim_full_code_def] >> qexists_tac `func` >> simp[]) >>
  `is_word_type (expr_type addr)` by simp[is_word_type_def] >>
  irule reached_word_result_bind_mods >>
  asm_rewrite_tac[] >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
  qexistsl_tac [`d`,`expr_vv_res_ok`,`aop`,`s2`,`s3`,`shadow_func`,`sh2`,`sh3`,`ty`] >>
  asm_rewrite_tac[] >>
  conj_tac
  >- simp[exprSimDefsTheory.expr_vv_res_ok_def,exprSimDefsTheory.expr_res_ok_def]
  >> suspend "address_success"
QED

Resume slice_external_address_bind_mods[address_success]:
  qx_genl_tac [`marks`,`v`,`ae`,`G3`,`tn3`,`z`] >> strip_tac >>
  `^entry ae s3 z G3 tn3 /\
   ^forced addr (fin with gas_obs := gas_explicit marks t2.vs_gas_readings) = (INL v,ae)` by
    (BETA_TAC >> irule (BETA_RULE slice_word_next_entry_mods) >>
     asm_rewrite_tac[] >> qexistsl_tac [`G2`,`aop`,`s2`,`tn2`] >> asm_rewrite_tac[]) >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `local_ptrs_reserved cenv s3 /\ _` strip_assume_tac >>
  qmatch_asmsub_abbrev_tac `fin with gas_obs := obs` >>
  `expr_body_pre_mods mods cenv cx env addr (fin with gas_obs := obs) /\
   body_const_cells_agree_mods mods cx env (fin with gas_obs := obs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `?bs. v = BytesV bs /\ LENGTH bs = 20` by
    (qpat_assum `value_runtime_typed _ _ v` mp_tac >>
     qpat_assum `expr_type addr = _` (fn th => PURE_REWRITE_TAC [th]) >>
     Cases_on `v` >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperValueTheory.evaluate_type_def,vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `v = BytesV _` SUBST_ALL_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon ae.storage_trace) ae.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ae.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `eval_operand aop z = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs))` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule exprSimPrecompilesTheory.expr_post_typed_stack_operand >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `post_value_type cenv addr = BaseT AddressT` by
    (qpat_assum `expr_type addr = _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     irule post_value_type_word >> first_assum ACCEPT_TAC) >>
  `op_prov G3 aop = NONE /\ op_taint tn3 aop = {}` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `post_value_type cenv addr = _` (fn th => PURE_REWRITE_TAC [th]) >>
     simp[bodyPtrDefsTheory.ptr_val_ok_def,is_word_type_def]) >>
  `(!q. aop = Var q ==> not_fresh_at s3 q) /\ (!l. aop <> Label l)` by
    (qpat_assum `expr_body_pre_mods _ _ _ _ addr fin`
       (mp_then Any assume_tac exprBodyPrePropsTheory.expr_body_pre_mods_well_typed) >>
     qpat_assum `expr_sim_inv_mods _ _ _ _ ae`
       (mp_then Any assume_tac exprBodyPrePropsTheory.expr_sim_inv_mods_env) >>
     drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
     `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
       (rpt strip_tac >> drule_all exprSimSourceTheory.env_consistent_var_type_evaluates >>
        simp[vyperTypeSystemTheory.well_formed_type_def]) >>
     drule_all_then strip_assume_tac exprWordOperandTheory.lower_value_word_shape >> simp[]) >>
  qpat_assum `!m b e G tn t. _ ==> gas_outcome_full_mods _ _ _ _ (next (BytesV b)) _ _ _` irule >>
  asm_rewrite_tac[] >> conj_tac
  >- (qexists_tac `marks` >> simp[Abbr `obs`]) >>
  qpat_assum `!H. valid_horizon _ _ H ae.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (fn th => simp[th])
QED

Finalise slice_external_address_bind_mods
