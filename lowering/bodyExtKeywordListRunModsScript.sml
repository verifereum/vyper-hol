(* Linked sequential simulation for the ExtCall keyword suffix. *)
Theory bodyExtKeywordListRunMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods exprLowering compileEnv
  gasOutcomeFullMods gasOutcomeFullPostMods gasShadow gasContext exprSimHypsDefs
  bodyInvSplit vyperInterpreter vyperState vyperTypeSystem vyperAST vyperContext
  loweringPosts loweringStateRelDefs bodyPtrDefs bodyFullShadowBodyInv
  bodyCallSupport bodyInvCodeProps list pair option finite_map arithmetic
  bodyExtKeywordListFoldMods bodyExtKeywordHeadRunMods bodyExtKeywordScalarJoinMods
  bodyExtKeywordScalarMods bodyExtKeywordDefaultMods
Libs
  monadsyntax

(* The linked counterpart of extcall_request_keywords_owned_outcome. *)
Theorem ext_kw_list_run_mods:
  body_exprs_full_ok_mods mods exps cx xs /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  (!e st. MEM e xs /\
    expr_sim_inv_mods mods cenv cx env st ==>
      expr_body_pre_mods mods cenv cx env e st) /\
  MAP expr_type xs = MAP (ext_call_kw_type rt) ks /\
  compile_ext_call_kwargs compile_expr cenv rt ks xs sa = ((vo,go,dopt),sb) /\
  compile_ext_call_kwargs compile_expr (gas_shadow_env T cenv) rt ks
    (MAP gas_shadow_expr xs) shadow_sa = ((vo,go,dopt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\
  alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
    dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
    (\H res ee G tn t. ?vs. res = INL vs /\ LENGTH vs = LENGTH xs /\
      expr_sim_inv_mods mods cenv cx env ee /\
      body_const_cells_agree_mods mods cx env ee /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~t.vs_halted /\
      alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\
      wb_frame cenv es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_labels = s0.vs_labels /\
      (case ext_call_kwarg EKGas ks vs of
         NONE => go = NONE
       | SOME v => ?op w. go = SOME op /\ eval_operand op t = SOME w /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
      (case ext_call_kwarg EKValue ks vs of
         NONE => vo = NONE
       | SOME v => ?op w. vo = SOME op /\ eval_operand op t = SOME w /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           dest_NumV v = SOME (w2n w) /\ op_taint tn op = {}) /\
      (case ext_call_kwarg EKDefault ks vs of
         NONE => dopt = NONE
       | SOME v => ?e op dt. dopt = SOME (op,dt) /\
           ext_call_kwarg EKDefault ks xs = SOME e /\
           (!x. op = Var x ==> not_fresh_at sb x) /\
           if is_word_type rt then
             dt = rt /\ expr_val_rel cx rt v op t /\ ptr_val_ok cx rt v op G tn t
           else dt = lowered_value_type cenv e /\
             ptr_val_ok cx dt v op G tn t /\
             ptr_mem_ok cx dt v op G tn t /\
             ptr_buf_ok cenv e op G t /\
             (!w. eval_operand op t = SOME w /\
               type_memory_bytes cenv dt <> 0 ==>
               w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
             (?w aid tv. eval_operand op t = SOME w /\
               evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv v /\
               FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
               aid < sb.cs_next_id)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule ext_kw_list_run_with_head_mods >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qexistsl [`exps`, `shadow_func`, `shadow_sa`, `shadow_sb`, `src`, `tops`] >>
  simp[] >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es'` by
    FAIL_TAC "reuse keyword_read_admissible" >>
  irule (CONV_RULE (DEPTH_CONV BETA_CONV) extcall_keyword_head_outcome_mods) >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (disch_tac >>
    irule (CONV_RULE (DEPTH_CONV BETA_CONV) ext_kw_scalar_join_mods) >> simp[] >>
    ntac 2 (conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >>
    conj_tac >- (disch_tac >>
      pure_rewrite_tac [GSYM CONJ_ASSOC] >>
      irule (PURE_REWRITE_RULE [GSYM CONJ_ASSOC] ext_kw_scalar_head_mods) >>
      simp[] >> ntac 2 (conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >>
      conj_tac >- (qexistsl [`env`, `mods`] >> simp[]) >>
      qexistsl [`k`, `rt`, `shadow_func`, `shadow_sa'`, `shadow_sb'`] >> simp[] >>
      conj_tac >- (Cases_on `k` >> gvs[] >>
        qpat_x_assum `compile_ext_call_kwarg compile_expr cenv _ _ _ _ = _` mp_tac >>
        simp[NoAsms, compile_ext_call_kwarg_def, comp_bind_def, comp_return_def,
                     ext_call_kw_type_def] >> pairarg_tac >> simp[]) >>
      conj_tac >- (Cases_on `k` >> gvs[] >>
        qpat_x_assum `compile_ext_call_kwarg compile_expr (gas_shadow_env T _) _ _ _ _ = _` mp_tac >>
        simp[NoAsms, compile_ext_call_kwarg_def, comp_bind_def, comp_return_def,
                     ext_call_kw_type_def] >> pairarg_tac >> simp[]) >>
      qpat_assum `body_expr_full_ok_mods _ _ _ _`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
      qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                    _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
        (FIRST o map irule o CONJUNCTS o REWRITE_RULE [IMP_CONJ_THM] o SPEC_ALL) >>
      simp[] >> conj_tac >- (qexistsl [`src`, `tops`] >> simp[]) >>
      qexists `env` >> simp[]) >>
    conj_tac >- (qexistsl [`shadow_func`, `shadow_sa'`, `shadow_sb'`] >> simp[]) >>
    conj_tac >- (qexists `exps` >> simp[]) >>
    conj_tac >- (qexistsl [`src`, `tops`] >> simp[]) >>
    qexists `env` >> simp[]) >>
  reverse conj_tac >- (qexists `exps` >> first_assum ACCEPT_TAC) >>
  strip_tac >> qpat_x_assum `k = EKDefault` SUBST_ALL_TAC >>
  drule_then (SUBST1_TAC o SYM) contract_inv_cenv_modules >>
  pure_rewrite_tac [GSYM CONJ_ASSOC] >>
  irule (PURE_REWRITE_RULE [GSYM CONJ_ASSOC] ext_kw_default_head_mods) >>
  fs[ext_call_kw_type_def] >>
  ntac 2 (conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[])) >>
  conj_tac >- (qexistsl [`shadow_func`, `shadow_sa'`, `shadow_sb'`] >> simp[]) >>
  qexistsl [`env`, `exps`, `mods`, `src`, `tops`] >> simp[]
QED
