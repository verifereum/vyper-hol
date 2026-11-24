Theory createSizeRawReplay
Ancestors
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragGasOrigin gasExplicitSites gasSummary s1PrefixDefs
  venomState vyperCreate vyperState relation list words createMarkedPath pair arithmetic
  exprLowering vfmConstants compileEnv exprLoweringProps exprBodyPreProps exprSimSource
  bodySimStmtFacts vyperStorageTrace rich_list exprSimHypsDefs vyperTypeSystem
  vyperTypeExprSoundness gasCount exprSimHyps bodyPtrDefs loweringPosts context
  createSizeRawSource fragGasPath vyperAST vyperStorageFootprint vyperValue integer_word
  valueEncoding loweringStateRelDefs exprSimMemDefs ptrDiscipline bodySim
  createExprSizeExitDefs createSizePrefixReplay createSizeCopyReplay
  createSizeBlueprintKeywordReplay createSizeOperandPre exprSimWordArgs vyperTyping

Theorem create_prefix_readings:
  create_expr_prefix sa sb explicit ctx func s ms t ==>
  t.vs_gas_readings = DROP (LENGTH ms) s.vs_gas_readings
Proof
  simp[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step sa sb explicit ctx func)) x y ==>
    ?n. LENGTH (SND y) = LENGTH (SND x) + n /\
        (FST y).vs_gas_readings = DROP n (FST x).vs_gas_readings`
    suffices_by (disch_then (qspecl_then [`(s,[])`,`(t,ms)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT_RIGHT1 >> simp[] >>
  map_every qx_gen_tac [`x`,`y`,`z`] >>
  map_every PairCases_on [`x`,`y`,`z`] >>
  simp[create_marked_edge_def, create_prefix_step_def, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  drule gas_origin_edge_erase >> strip_tac >>
  drule gas_path_edge_suffix >> simp[gas_count_suffix_def] >> strip_tac >>
  qexists_tac `LENGTH ms + n` >> simp[DROP_DROP_T, AC ADD_ASSOC ADD_COMM]
QED

Theorem raw_decoded_keywords[local]:
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

(* The same read law is used at both keyword cuts. B is the
   source-side guard under which the caller can supply value replay. *)
Definition raw_scalar_read_law_def:
  raw_scalar_read_law B (DF,lo,d,ctx,shctx,fnc,shfnc) tops ce cx env st0 <=>
  !e p ca cb sca scb op u G tn chunk t rest k res out H tail.
    B e p /\ expr_body_pre ce cx env e p /\
    lower_value compile_expr ce (expr_type e) e ca = (op,cb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (op,scb) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
    local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
    return_buf_frame d ce ca u /\ alloca_history fnc u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
      ghost_inv_at (DF h) lo d ce cx p G tn u) /\
    ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\
    u.vs_inst_idx = LENGTH ca.cs_current_insts /\
    create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
    t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
    (!v. storage_trace_frame (k v)) /\
    bind (bind (eval_expr cx e) (read_result cx)) k p = ((res : eval_result + exception),out) /\
    valid_horizon cx st0 H out.storage_trace /\
    p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
    ?v q G' tn'.
      bind (eval_expr cx e) (read_result cx) p = (INL v,q) /\ k v q = (res,out) /\
      q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
      valid_horizon cx st0 H q.storage_trace /\
      expr_sim_inv ce cx env q /\ value_runtime_typed env (expr_type e) v /\
      expr_val_rel cx (post_value_type ce e) v op t /\
      ca.cs_next_var <= cb.cs_next_var /\
      (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
      return_buf_frame d ce cb t /\ alloca_history fnc t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
      (!h. valid_horizon cx st0 h q.storage_trace ==>
        stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
        ghost_inv_at (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
End

Theorem raw_scalar_read_law_completed[local]:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx ==>
  raw_scalar_read_law (\e p. create_operand_completed_ok cx e)
    (DF,lo,d,ctx,shctx,fnc,shfnc) tops ce cx env st0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  pure_rewrite_tac[raw_scalar_read_law_def] >> BETA_TAC >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL (INST_TYPE [alpha |-> ``:eval_result``] blueprint_read_at_cut)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Theorem create_raw_keywords_from_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) args df) entry /\
  args = e::av::(xs ++ (if hs then [salt] else [])) /\
  raw_scalar_read_law B (DF,lo,d,ctx,shctx,fnc,shfnc) tops ce cx env st0 /\
  B av p /\
  (hs ==> !va pa. bind (eval_expr cx av) (read_result cx) p = (INL va,pa) /\
      value_runtime_typed env (expr_type av) va ==> B salt pa) /\
  LENGTH cvs = LENGTH xs /\ expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
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
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
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

  `expr_type av = BaseT (UintT 256) /\ (hs ==> expr_type salt = BaseT (BytesT (Fixed 32)))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def,
                          LAST_APPEND_CONS, FRONT_APPEND]) >>
  `expr_body_pre ce cx env av p` by
    (irule create_call_operand_body_pre >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  qabbrev_tac `ka = \v. bind (eval_exprs cx (if hs then [salt] else [])) (\vs. kfinal (v::vs))` >>
  `bind (bind (eval_expr cx av) (read_result cx)) ka p = (res,out)` by
    fs[Abbr `ka`,create_copy_source_cons] >>
  `!v. storage_trace_frame (ka v)` by simp[Abbr `ka`, blueprint_read_list_frame] >>
  qhdtm_assum `raw_scalar_read_law` (fn th =>
    mp_tac (Q.INST [`e` |-> `av`, `cb` |-> `cm`, `scb` |-> `scm`,
                    `op` |-> `amount_op`, `chunk` |-> `ma`, `t` |-> `m`,
                    `rest` |-> `ms`, `k` |-> `ka`]
             (SPEC_ALL (REWRITE_RULE [raw_scalar_read_law_def] th)))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx av) (read_result cx) p = (INL avalue,pa)` >>
  rename1 `ghost_inv_at (DF _) lo d ce cx pa Ga tna m` >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  qabbrev_tac `ksalt = \svs. kfinal (avalue::svs)` >>
  `bind (eval_exprs cx (if hs then [salt] else [])) ksalt pa = (res,out)` by
    fs[Abbr `ka`, Abbr `ksalt`] >>
  `!svs. storage_trace_frame (ksalt svs)` by simp[Abbr `ksalt`] >>
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?svs q. ksalt svs q = (res,out) /\
     (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) /\
     (!x w. not_fresh_at cm x /\ lookup_var x m = SOME w ==> lookup_var x n = SOME w)` by
    (suspend "salt") >>
  pop_assum strip_assume_tac >- metis_tac[] >>
  `?amt. dest_NumV avalue = SOME amt` by
    (qpat_assum `expr_type av = _` (fn th =>
       qpat_assum `value_runtime_typed env (expr_type av) avalue`
         (mp_tac o MATCH_MP blueprint_keyword_uint o REWRITE_RULE[th])) >> metis_tac[]) >>
  drule_all raw_decoded_keywords >> disch_then (qspecl_then [`cvs`,`code`] strip_assume_tac) >>
  disj2_tac >> qexistsl [`BytesV code::(cvs ++ avalue::svs)`,`ops`,`q`] >>
  Cases_on `hs` >> gvs[create_arg_ctor_types_def, FRONT_APPEND]
QED

Resume create_raw_keywords_from_replay[salt]:
  reverse (Cases_on `hs`)
  >- (disj2_tac >> qexistsl [`[]`,`pa`] >>
      fs[eval_exprs_nil,bind_def]) >>
  qpat_x_assum `if T then _ else _`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss []) >>
  `B salt pa` by metis_tac[] >>
  `expr_body_pre ce cx env salt pa` by
    (irule create_call_operand_body_pre >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `bind (bind (eval_expr cx salt) (read_result cx)) (\v. ksalt [v]) pa = (res,out)` by
    fs[create_copy_source_cons, cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  qhdtm_assum `raw_scalar_read_law` (fn th =>
    mp_tac (BETA_RULE (Q.INST [`e` |-> `salt`, `p` |-> `pa`, `ca` |-> `cm`,
      `cb` |-> `cn`, `sca` |-> `scm`, `scb` |-> `scn`, `op` |-> `salt_op`,
      `u` |-> `m`, `G` |-> `Ga`, `tn` |-> `tna`, `chunk` |-> `ms`, `t` |-> `n`,
      `rest` |-> `[]`, `k` |-> `\v. ksalt [v]`]
             (SPEC_ALL (REWRITE_RULE [raw_scalar_read_law_def] th))))) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  strip_tac >- metis_tac[] >>
  rename1 `bind (eval_expr cx salt) (read_result cx) pa = (INL sval,q)` >>
  `expr_type salt = BaseT (BytesT (Fixed 32))` by fs[] >>
  `?w. dest_create_salt sval = SOME w` by
    (qpat_assum `value_runtime_typed env (expr_type salt) sval` mp_tac >>
     qpat_assum `expr_type salt = _` (pure_rewrite_tac o single) >>
     Cases_on `sval` >>
     simp_tac (srw_ss()) [value_runtime_typed_def, evaluate_type_def,
                          value_has_type_def, dest_create_salt_def, dest_BytesV_def]) >>
  disj2_tac >> qexistsl [`[sval]`,`q`] >> simp[]
QED
Finalise create_raw_keywords_from_replay

Theorem create_raw_keywords_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) args df) entry /\
  args = e::av::(xs ++ (if hs then [salt] else [])) /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs args) /\
  LENGTH cvs = LENGTH xs /\ expr_sim_inv ce cx env p /\
  local_ptrs_reserved ce ca /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
    stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
    ghost_inv_at (DF h) lo d ce cx p G tn u) /\
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
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
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
  `create_operand_completed_ok cx av /\ (hs ==> create_operand_completed_ok cx salt)` by
    (qpat_assum `args = _` (fn th => qhdtm_assum `EVERY` (mp_tac o REWRITE_RULE[th])) >>
     Cases_on `hs` >> simp[create_operand_order_def, EVERY_APPEND,
                          DROP_PREFIX, TAKE_APPEND1]) >>
  mp_tac (BETA_RULE (Q.INST [`B` |-> `\e p. create_operand_completed_ok cx e`]
                          (SPEC_ALL create_raw_keywords_from_replay))) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
    >- (irule raw_scalar_read_law_completed >> simp[]) >>
    simp[])) >> disch_then ACCEPT_TAC
QED

Theorem create_raw_first_full_pre[local]:
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,a) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_a) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,a,shadow_sa,shadow_a) /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty parent es (st0,sa,sb,shadow_sa,shadow_sb,parent_vv,s0,G0,tn0) ==>
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0)
Proof
  simp[expr_vv_sim_full_pre_def, expr_sim_full_code_def] >>
  metis_tac[expr_body_pre_vv_gas_admissible]
QED

(* Fixed-site request: the caller supplies replay only at this paired
   bytecode-child entry, not at arbitrary invocations of e. *)
Definition raw_bytecode_replay_at_def:
  raw_bytecode_replay_at (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    tops ce cx env e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0) <=>
  (expr_body_pre ce cx env e es /\
   expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0) ==>
   gas_completed_operand (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     tops cx st0 sa a (eval_expr cx e) (es,s0,G0,tn0)
     (\H res ee G tn t. ?tv. res = INL tv /\
       vv_post H ctx func ce cx e es sa a s0 ee tv vv t /\
       vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
       alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
       s0.vs_alloca_next <= t.vs_alloca_next /\
       ghost_inv_at (DF H) lo dep ce cx ee G tn t /\
       ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn t /\
       (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
          ~is_bytestring_type (post_value_type ce e) ==>
          vv_own ce cx (post_value_type ce e) sa a ee tv vv t /\
          (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                 eval_operand (vv_operand vv) t = SOME w ==>
                 w2n w + type_memory_size rt <= lo /\
                 (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                        val_in_memory rt val (w2n w) mem)) /\
       (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce e) ==>
          ptr_buf_ok ce e op G t) /\
       (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce e p.ptr_operand G t) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 G tn))
End

Theorem raw_bytecode_replay_at_of_completed:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs (e::v::rest)) ==>
  raw_bytecode_replay_at (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    tops ce cx env e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0)
Proof
  strip_tac >>
  `create_operand_completed_ok cx e` by fs[create_operand_order_def] >>
  pure_rewrite_tac[raw_bytecode_replay_at_def] >> strip_tac >>
  drule_all create_size_replay_vv_cut >> simp[]
QED

Theorem create_raw_bytecode_replay_from_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  raw_bytecode_replay_at (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
    tops ce cx env e es (st0,sa,a,shadow_sa,shadow_a,vv,s0,G0,tn0) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
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
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
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
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    !h. valid_horizon cx st0 h p.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) ms (OK u,G,tn) /\
      vv_post h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env e es` by
    (drule exprBodyPrePropsTheory.expr_body_pre_static_facts >> strip_tac >>
     `MEM e (e::v::rest)` by simp[] >> metis_tac[create_call_operand_body_pre]) >>
  drule_all create_raw_first_full_pre >> strip_tac >>
  qhdtm_x_assum `raw_bytecode_replay_at`
    (fn th => mp_tac (REWRITE_RULE [raw_bytecode_replay_at_def] th)) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  qpat_x_assum `eval_expr _ (Call _ _ _ _) _ = _`
    (assume_tac o REWRITE_RULE[create_raw_call_split]) >>
  qmatch_asmsub_abbrev_tac `es with gas_obs := gs` >>
  `?head_res p. eval_expr cx e (es with gas_obs := gs) = (head_res,p)` by
    (Cases_on `eval_expr cx e (es with gas_obs := gs)` >> simp[]) >>
  `valid_horizon cx st0 H p.storage_trace` by metis_tac[create_raw_cont_horizon] >>
  `gs = gas_explicit ms s0.vs_gas_readings ++ (gas_explicit later u.vs_gas_readings ++ tail)` by
    (drule create_prefix_readings >> simp[Abbr `gs`, gas_explicit_append, APPEND_ASSOC]) >>
  qpat_x_assum `gas_completed_operand _ _ _ _ _ _ _ _ _`
    (qspecl_then [`H`,`ms`,`u`,`gas_explicit later u.vs_gas_readings ++ tail`,`head_res`,`p`] mp_tac
      o REWRITE_RULE[gas_completed_operand_def]) >>
  (impl_tac >- (qpat_assum `gs = gas_explicit _ _ ++ (_ ++ _)`
      (fn th => PURE_REWRITE_TAC[GSYM th]) >> simp[])) >>
  strip_tac
  >- (`well_typed_expr env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df)` by
        metis_tac[exprBodyPrePropsTheory.expr_body_pre_static_facts] >>
      drule create_raw_first_type >> strip_tac >>
      qpat_assum `!h. valid_horizon _ _ h _ ==> _`
        (mp_tac o BETA_RULE o Q.SPEC `H`) >>
      asm_rewrite_tac[] >> disch_then strip_assume_tac >>
      qpat_x_assum `head_res = INL _` SUBST_ALL_TAC >>
      drule_all create_raw_read_bytes >> strip_tac >>
      `expr_sim_inv ce cx env p` by
        (`expr_body_pre ce cx env e (es with gas_obs := gs)` by
          simp[exprSimSourceTheory.expr_body_pre_gas_obs] >>
         metis_tac[exprSimSourceTheory.expr_body_pre_eval_result]) >>
      disj2_tac >> qexistsl_tac [`p`,`tv`,`code`,`G`,`tn`,`n`] >>
      simp[] >> conj_tac
      >- (qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >>
          simp[bind_def]) >>
      rpt strip_tac >>
      first_x_assum (drule_then strip_assume_tac) >> gvs[]) >>
  disj1_tac >> qexists_tac `err` >>
  qpat_x_assum `bind (eval_expr _ _) _ _ = _` mp_tac >> simp[bind_def]
QED

Theorem create_raw_bytecode_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget RawCreate hs rof ks) (e::v::rest) df) es /\
  EVERY (create_operand_completed_ok cx) (create_operand_order RawCreate hs (e::v::rest)) /\
  expr_vv_sim_full_pre (DF,lo,dep,ctx,shadow_ctx,PG,func,shadow_func)
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
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
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
    valid_horizon cx st0 H p.storage_trace /\ expr_sim_inv ce cx env p /\
    !h. valid_horizon cx st0 h p.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) ms (OK u,G,tn) /\
      vv_post h ctx func ce cx e es sa a s0 (p with gas_obs := []) tv vv u /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) (p with gas_obs := []) tv vv u /\
      alloca_history func u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
      s0.vs_alloca_next <= u.vs_alloca_next /\
      ghost_inv_at (DF h) lo dep ce cx (p with gas_obs := []) G tn u /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_bytecode_replay_at_of_completed >> disch_tac >>
  mp_tac (SPEC_ALL create_raw_bytecode_replay_from_replay) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  disch_then ACCEPT_TAC
QED
