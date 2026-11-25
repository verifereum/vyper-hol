Theory createSizeRawReplayMods
Ancestors
  createSizeRawReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragGasOrigin gasExplicitSites gasSummary s1PrefixDefs
  venomState vyperCreate vyperState relation list words createMarkedPath pair arithmetic
  exprLowering vfmConstants compileEnv exprLoweringProps exprBodyPreProps exprSimSource
  bodySimStmtFacts vyperStorageTrace rich_list exprSimHypsDefs vyperTypeSystem
  vyperTypeExprSoundness gasCount exprSimHyps bodyPtrDefs loweringPosts context
  createSizeRawSourceMods fragGasPath vyperAST vyperStorageFootprint vyperValue integer_word
  valueEncoding loweringStateRelDefs exprSimMemDefs ptrDiscipline bodySim
  createExprSizeExitDefs createSizePrefixReplayMods createSizeCopyReplayMods
  createSizeBlueprintKeywordReplayMods createSizeOperandPreMods

Theorem raw_decoded_keywords_mods[local]:
  dest_NumV av = SOME amount /\
  (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) ==>
  ?ops. dest_create_args RawCreate hs
    (create_operand_layout RawCreate hs (BytesV code::(cvs ++ av::svs))) = SOME ops /\
    ops.co_code_src = BytecodeCodeSource code /\ ops.co_ctor_args = cvs
Proof
  Cases_on `hs` >> simp[] >> strip_tac >>
  gvs[create_operand_layout_def, dest_create_args_def, make_create_operands_def,
      dest_BytesV_def, dest_optional_num_def, dest_optional_salt_def,
      DROP_PREFIX, TAKE_APPEND1, FRONT_APPEND, LAST_APPEND_CONS]
QED


Theorem create_raw_keywords_at_cuts_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget RawCreate hs rof ks) args df) entry /\
  args = e::av::(xs ++ (if hs then [salt] else [])) /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order RawCreate hs args) /\
  LENGTH cvs = LENGTH xs /\ expr_sim_inv_mods mods ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\
    immutable_frame_mods fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at_mods (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
  u.vs_inst_idx = LENGTH ca.cs_current_insts /\
  lower_value compile_expr ce (expr_type av) av ca = (amount_op,cm) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type av) (gas_shadow_expr av) sca = (amount_op,scm) /\
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
  bind (eval_exprs cx (av::(if hs then [salt] else [])))
    (\kvs. eval_create_operands cx RawCreate hs rof
      (MAP expr_type args) (blueprint_literal_offset cx hs args)
      (BytesV code::(cvs ++ kvs))) p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (ma ++ ms) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?vs ops q.
    eval_create_operands cx RawCreate hs rof (MAP expr_type args)
      (blueprint_literal_offset cx hs args) vs q = (res,out) /\
    dest_create_args RawCreate hs (create_operand_layout RawCreate hs vs) = SOME ops /\
    ops.co_code_src = BytecodeCodeSource code /\ ops.co_ctor_args = cvs /\
    create_arg_ctor_types RawCreate hs (MAP expr_type args) = SOME (MAP expr_type xs) /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x m = SOME w) /\
    ca.cs_next_var <= cm.cs_next_var /\
    (!x w. not_fresh_at cm x /\ lookup_var x m = SOME w ==> lookup_var x n = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `kfinal = \kvs. eval_create_operands cx RawCreate hs rof
    (MAP expr_type args) (blueprint_literal_offset cx hs args) (BytesV code::(cvs ++ kvs))` >>
  `!kvs. storage_trace_frame (kfinal kvs)` by simp[Abbr `kfinal`, storage_trace_frame_create_operands] >>
  `create_operand_completed_ok_mods mods exps cx av /\ (hs ==> create_operand_completed_ok_mods mods exps cx salt)` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def, EVERY_APPEND,
                          DROP_PREFIX, TAKE_APPEND1]) >>
  `expr_type av = BaseT (UintT 256) /\ (hs ==> expr_type salt = BaseT (BytesT (Fixed 32)))` by
    (drule exprBodyPreTypingPropsTheory.expr_body_pre_mods_runtime_typing >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def,
                          LAST_APPEND_CONS, FRONT_APPEND]) >>
  `expr_body_pre_mods mods ce cx env av p` by
    (irule create_call_operand_body_pre_mods >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ka = \v. bind (eval_exprs cx (if hs then [salt] else [])) (\vs. kfinal (v::vs))` >>
  `bind (bind (eval_expr cx av) (read_result cx)) ka p = (res,out)` by
    fs[Abbr `ka`, createSizeCopyReplayTheory.create_copy_source_cons] >>
  `!v. storage_trace_frame (ka v)` by simp[Abbr `ka`, createSizeBlueprintKeywordReplayTheory.blueprint_read_list_frame] >>
  drule_all blueprint_read_at_cut_mods >> strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx av) (read_result cx) p = (INL avalue,pa)` >>
  drule_all createSizeBlueprintKeywordReplayTheory.blueprint_keyword_mono >> strip_tac >>
  `hs ==> expr_body_pre_mods mods ce cx env salt pa /\ create_operand_completed_ok_mods mods exps cx salt /\
      expr_type salt = BaseT (BytesT (Fixed 32))` by
    (strip_tac >> simp[] >> irule create_call_operand_body_pre_mods >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ksalt = \svs. kfinal (avalue::svs)` >>
  `bind (eval_exprs cx (if hs then [salt] else [])) ksalt pa = (res,out)` by
    fs[Abbr `ka`, Abbr `ksalt`] >>
  `!svs. storage_trace_frame (ksalt svs)` by simp[Abbr `ksalt`] >>
  drule_all (SIMP_RULE (srw_ss()) [] (Q.INST [`rest` |-> `[]`] createSizeBlueprintKeywordReplayModsTheory.blueprint_optional_salt_at_cut_mods)) >>
  strip_tac >- metis_tac[] >>
  `?amt. dest_NumV avalue = SOME amt` by
    (qpat_assum `expr_type av = _` (fn th =>
       qpat_assum `value_runtime_typed env (expr_type av) avalue`
         (mp_tac o MATCH_MP createSizeBlueprintKeywordReplayTheory.blueprint_keyword_uint o REWRITE_RULE[th])) >> metis_tac[]) >>
  drule_all raw_decoded_keywords_mods >> disch_then (qspecl_then [`cvs`,`code`] strip_assume_tac) >>
  disj2_tac >> qexistsl [`BytesV code::(cvs ++ avalue::svs)`,`ops`,`q`] >>
  Cases_on `hs` >> gvs[create_arg_ctor_types_def, FRONT_APPEND]
QED

Theorem create_raw_first_full_pre_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty parent es (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) ==>
  expr_vv_sim_full_pre_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0)
Proof
  cheat
QED

Theorem create_raw_bytecode_replay_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  expr_body_pre_mods mods ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok_mods mods exps cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre_mods (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es
    (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  create_expr_prefix sa a (gas_explicit_sites ctx shadow_ctx) ctx func s0 ms u /\
  u.vs_current_bb = a.cs_current_bb /\ u.vs_inst_idx = LENGTH a.cs_current_insts /\
  eval_expr cx (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df)
    (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?p tv code G tn n.
    expr_type e = BaseT (BytesT (Dynamic n)) /\ LENGTH code <= n /\ n <= 49152 /\
    eval_expr cx e (es with gas_obs := gas_explicit (ms ++ later) s0.vs_gas_readings ++ tail) = (INL tv,p) /\
    p.gas_obs = gas_explicit later u.vs_gas_readings ++ tail /\
    read_result cx tv p = (INL (BytesV code),p) /\
    read_result cx tv (p with gas_obs := []) = (INL (BytesV code),p with gas_obs := []) /\
    bind (eval_exprs cx (TAKE (LENGTH rest - (if hs then 1 else 0)) rest ++
                       v :: DROP (LENGTH rest - (if hs then 1 else 0)) rest))
      (\vs. eval_create_operands cx RawCreate hs rof (MAP expr_type (e::v::rest))
        (blueprint_literal_offset cx hs (e::v::rest)) (BytesV code::vs)) p = (res,ee) /\
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv_mods mods ce cx env p /\
    !h. valid_horizon cx st0 h p.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) ms (OK u,G,tn) /\
      vv_post_mods h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at_mods (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
      ptr_vv_ok cx (post_value_type ce e) tv vv (p with gas_obs := []) G tn u /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) u = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
                      val_in_memory rt (BytesV code) (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G u) /\
      (!t' ptr. vv = LocatedValue t' ptr /\ ptr.ptr_location = LocMemory ==>
               ptr_buf_ok ce e ptr.ptr_operand G u) /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn
Proof
  cheat
QED
