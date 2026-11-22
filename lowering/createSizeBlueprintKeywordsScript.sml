Theory createSizeBlueprintKeywords
Ancestors
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps gasExplicitSites gasSummary venomState vyperCreate
  vyperState relation list words pair arithmetic exprLowering vfmConstants exprLoweringProps
  exprBodyPreProps vyperStorageTrace freshWrites rich_list exprSimHypsDefs vyperTypeSystem
  vyperTypeExprSoundness exprSimWordArgs bodyPtrDefs loweringPosts vyperAST
  vyperStorageFootprint vyperValue integer_word loweringStateRelDefs ptrDiscipline bodySim
  loweringShapeDefs createExprSizeExitDefs createSizeCopyReplay
  createSizeBlueprintKeywordReplay createSizeOperandPre createSizePrefixReplay

Theorem create_blueprint_keywords_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order (CreateFromBlueprint raw) hs args) /\
  LENGTH cvs = LENGTH ctors /\ dest_AddressV av = SOME (w2w aw) /\
  eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_no_wrap i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  lower_value compile_expr ce (expr_type amount) amount ca = (amount_op,cm) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type amount) (gas_shadow_expr amount) sca = (amount_op,scm) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cm,sca,scm) /\
  create_expr_prefix ca cm (gas_explicit_sites ctx shctx) ctx fnc u ma m /\
  m.vs_current_bb = cm.cs_current_bb /\ m.vs_inst_idx = LENGTH cm.cs_current_insts /\
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt cm = (salt_op,cn) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) scm = (salt_op,scn) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (cm,cn,scm,scn) /\
      create_expr_prefix cm cn (gas_explicit_sites ctx shctx) ctx fnc m ms n /\
      n.vs_current_bb = cn.cs_current_bb /\ n.vs_inst_idx = LENGTH cn.cs_current_insts
   else cn = cm /\ scn = scm /\ n = m /\ ms = []) /\
  ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
     offset_op = Lit (i2w i) /\ cb = cn /\ scb = scn /\ t = n /\ mo = []) \/
   (lower_value compile_expr ce (expr_type off) off cn = (offset_op,cb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) scn = (offset_op,scb) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (cn,cb,scn,scb) /\
    create_expr_prefix cn cb (gas_explicit_sites ctx shctx) ctx fnc n mo t /\
    t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts)) /\
  bind (eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])))
    (\kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (ma ++ (ms ++ (mo ++ rest))) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?kvs q ops ow.
    eval_exprs cx (amount::((if hs then [salt] else []) ++ [off])) p = (INL kvs,q) /\
    eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs)) q = (res,out) /\
    dest_create_args (CreateFromBlueprint raw) hs
      (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ kvs))) = SOME ops /\
    ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME (w2n ow) /\
    eval_operand target_op t = SOME aw /\ eval_operand offset_op t = SOME ow /\
    (!x. offset_op = Var x ==> not_fresh_at cb x) /\
    (lookup_account (w2w aw) q.accounts).code = (lookup_account (w2w aw) t.vs_accounts).code /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `kfinal = \kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))` >>
  `!kvs. storage_trace_frame (kfinal kvs)` by simp[Abbr `kfinal`, storage_trace_frame_create_operands] >>
  `create_operand_completed_ok cx amount /\ (hs ==> create_operand_completed_ok cx salt) /\
     create_operand_completed_ok cx off` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def, EVERY_APPEND]) >>
  `expr_type amount = BaseT (UintT 256) /\ (hs ==> expr_type salt = BaseT (BytesT (Fixed 32)))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def]) >>
  `expr_body_pre ce cx env amount p` by
    (irule create_call_operand_body_pre >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ka = \v. bind (eval_exprs cx ((if hs then [salt] else []) ++ [off])) (\vs. kfinal (v::vs))` >>
  `bind (bind (eval_expr cx amount) (read_result cx)) ka p = (res,out)` by fs[Abbr `ka`,create_copy_source_cons] >>
  `!v. storage_trace_frame (ka v)` by simp[Abbr `ka`, blueprint_read_list_frame] >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx amount) (read_result cx) p = (INL avalue,pa)` >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  `hs ==> expr_body_pre ce cx env salt pa /\ create_operand_completed_ok cx salt /\
      expr_type salt = BaseT (BytesT (Fixed 32))` by
    (strip_tac >> simp[] >> irule create_call_operand_body_pre >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ksalt = \svs. bind (eval_exprs cx [off]) (\ovs. kfinal (avalue::(svs ++ ovs)))` >>
  `bind (eval_exprs cx (if hs then [salt] else [])) ksalt pa = (res,out)` by
    fs[Abbr `ka`, Abbr `ksalt`, blueprint_eval_salt_offset] >>
  `!svs. storage_trace_frame (ksalt svs)` by
    simp[Abbr `ksalt`, evaluate_storage_trace_frame, storage_trace_frame_bind_all] >>
  drule_all blueprint_optional_salt_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `eval_exprs cx (if hs then [salt] else []) pa = (INL salts,ps)` >>
  `ca.cs_next_var <= cn.cs_next_var` by decide_tac >>
  drule_all (Q.INST [`cb` |-> `cn`] blueprint_keyword_mono) >> strip_tac >>
  `n.vs_current_bb = cn.cs_current_bb /\ n.vs_inst_idx = LENGTH cn.cs_current_insts` by
    (qpat_assum `if hs then _ else _` mp_tac >> Cases_on `hs` >> simp[] >> metis_tac[]) >>
  qabbrev_tac `koff = \ov. kfinal (avalue::(salts ++ [ov]))` >>
  `bind (bind (eval_expr cx off) (read_result cx)) koff ps = (res,out)` by
    fs[Abbr `ksalt`, Abbr `koff`, create_copy_source_cons, cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  `!ov. storage_trace_frame (koff ov)` by simp[Abbr `koff`] >>
  drule_all blueprint_offset_at_cut >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx off) (read_result cx) ps = (INL ov,qp)` >>
  `eval_exprs cx [off] ps = (INL [ov],qp)` by
    (irule blueprint_eval_join_cons >> metis_tac[eval_exprs_nil]) >>
  drule_all blueprint_eval_join_salt_offset >> strip_tac >>
  `?amt. dest_NumV avalue = SOME amt` by
    (qpat_assum `expr_type amount = _` (fn th =>
       qpat_assum `value_runtime_typed env (expr_type amount) avalue`
         (mp_tac o MATCH_MP blueprint_keyword_uint o REWRITE_RULE[th])) >> metis_tac[]) >>
  `?ops. dest_create_args (CreateFromBlueprint raw) hs
       (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ avalue::(salts ++ [ov])))) = SOME ops /\
     ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
     ops.co_code_offset = SOME (w2n w)` by
    (irule blueprint_decoded_keywords >> simp[] >> metis_tac[]) >>
  `!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at cm x /\ not_fresh_at cn x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  `m.vs_labels = u.vs_labels` by
    (qpat_assum `create_expr_prefix ca cm _ _ _ u ma m` (mp_then Any mp_tac create_prefix_labels) >> simp[]) >>
  `n.vs_labels = m.vs_labels` by
    (qpat_x_assum `if hs then lower_value _ _ _ salt cm = _ /\ _ else _` mp_tac >>
     reverse (Cases_on `hs`) >> pure_rewrite_tac[COND_CLAUSES]
     >- (strip_tac >> fs[]) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `create_expr_prefix cm cn _ _ _ m ms n`
       (mp_then Any mp_tac create_prefix_labels) >> simp[]) >>
  `t.vs_labels = n.vs_labels` by
    (qpat_x_assum `(?oty i. origin_fold_value off = _ /\ _) \/ _` strip_assume_tac
     >- simp[] >>
     qpat_assum `create_expr_prefix cn cb _ _ _ n mo t`
       (mp_then Any mp_tac create_prefix_labels) >> simp[]) >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >> qexistsl [`ca`,`u`] >> simp[] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`avalue::(salts ++ [ov])`, `qp`, `ops`, `w`] >> simp[] >>
  conj_tac >- (irule blueprint_eval_join_cons >> qexists_tac `pa` >> simp[]) >>
  drule blueprint_lookup_code >> simp[]
QED
