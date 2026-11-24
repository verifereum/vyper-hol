Theory createSizeBlueprintKeywordReplay
Ancestors
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragGasOrigin gasExplicitSites gasSummary s1PrefixDefs
  venomExecSemantics venomState vyperCreate vyperState relation list words createMarkedPath
  pair bodyFullIfExpReach arithmetic exprLowering vfmConstants compileEnv exprLoweringProps
  exprBodyPreProps exprSimSource bodySimStmtFacts vyperStorageTrace gasSummaryCompose
  bodyMemoryDefs exprOperandVar freshWrites rich_list exprSimHypsDefs
  createSizeBlueprintOffset vyperTypeSystem vyperTypeExprSoundness exprSimWordArgs
  accountsRelProps bodyPtrDefs loweringPosts fragGasPath vyperAST vyperStorageFootprint
  vyperTyping vyperValue integer_word valueEncoding loweringStateRelDefs ptrDiscipline
  bodySim loweringShapeDefs createExprSizeExitDefs createSizePrefixReplay
  createSizeCopyReplay createSizeOperandPre entryCreateBlueprintReadCut

Theorem blueprint_read_at_cut:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
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
  bind (bind (eval_expr cx e) (read_result cx)) k p = (res,out) /\
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
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (Q.INST [`PG` |-> `[]:(num # num) option list`]
    blueprint_read_at_cut_from_replay) >>
  rpt (goal_assum (drule_at Any)) >>
  simp[] >> metis_tac[create_size_replay_value_cut]
QED

Theorem blueprint_read_list_frame:
  (!xs. storage_trace_frame (k xs)) ==>
  !v. storage_trace_frame (bind (eval_exprs cx es) (\vs. k (v::vs)))
Proof
  simp[evaluate_storage_trace_frame, storage_trace_frame_bind_all]
QED

Theorem blueprint_keyword_uint:
  value_runtime_typed env (BaseT (UintT 256)) v ==>
  ?i. v = IntV i /\ dest_NumV v = SOME (w2n (i2w i : bytes32))
Proof
  Cases_on `v` >> simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def,
                       dimword_def] >> rpt strip_tac >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  simp[dest_NumV_def, i2w_def, w2n_n2w, dimword_def]
QED

Theorem blueprint_keyword_uint_word[local]:
  value_runtime_typed env (BaseT (UintT 256)) v /\
  expr_val_rel cx (BaseT (UintT 256)) v op t ==>
  ?w. dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w
Proof
  strip_tac >> drule blueprint_keyword_uint >> strip_tac >>
  gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
      typed_val_to_w256_def, val_to_w256_def]
QED

Theorem blueprint_keyword_salt[local]:
  value_runtime_typed env (BaseT (BytesT (Fixed 32))) v ==>
  ?w. dest_create_salt v = SOME w
Proof
  Cases_on `v` >> simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def,
                        dest_create_salt_def, dest_BytesV_def]
QED

Theorem blueprint_lookup_code:
  stmt_state_rel H ctx fnc ce cx st t ==>
  (lookup_account addr st.accounts).code = (lookup_account addr t.vs_accounts).code
Proof
  simp[stmt_state_rel_def] >> strip_tac >> drule state_rel_accounts >>
  strip_tac >> drule accounts_agree_lookup >> simp[]
QED

Theorem blueprint_offset_at_cut:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  create_operand_completed_ok cx off /\
  expr_sim_inv ce cx env p /\
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
  ((?oty i. origin_fold_value off = Literal oty (IntL i) /\
     op = Lit (i2w i) /\ cb = ca /\ scb = sca /\ t = u /\ chunk = []) \/
   (lower_value compile_expr ce (expr_type off) off ca = (op,cb) /\
    lower_value compile_expr (gas_shadow_env T ce) (expr_type off) (gas_shadow_expr off) sca = (op,scb) /\
    expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
    create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
    t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts)) /\
  (!v. storage_trace_frame (k v)) /\
  bind (bind (eval_expr cx off) (read_result cx)) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v q w.
    bind (eval_expr cx off) (read_result cx) p = (INL v,q) /\ k v q = (res,out) /\
    dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w /\
    stmt_state_rel H ctx fnc ce cx q t /\
    (!x. op = Var x ==> not_fresh_at cb x) /\
    (!x k. not_fresh_at ca x /\ lookup_var x u = SOME k ==> lookup_var x t = SOME k)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type off = BaseT (UintT 256)` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def]) >>
  qpat_x_assum `(?oty i. _) \/ _` strip_assume_tac
  >- (drule_all create_blueprint_offset_bridge >> strip_tac >>
      gvs[eval_operand_def] >>
      disj2_tac >> `k (IntV i) p = (res,out)` by
        (qpat_assum `!st. bind _ _ st = (INL _,st)` (qspec_then `p` assume_tac) >>
         fs[bind_def]) >>
      `valid_horizon cx st0 H p.storage_trace` by metis_tac[vyperStorageFootprintTheory.valid_horizon_frame] >>
      metis_tac[]) >>
  `expr_body_pre ce cx env off p` by
    (irule create_call_operand_body_pre >> simp[] >>
     goal_assum (drule_at Any) >> Cases_on `hs` >> simp[]) >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  disj2_tac >> qexistsl [`v`,`q`] >> simp[] >>
  `is_word_type (expr_type off)` by simp[is_word_type_def] >>
  `?w. dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w` by
    (irule blueprint_keyword_uint_word >> gvs[post_value_type_word] >>
     metis_tac[]) >>
  `!x. op = Var x ==> not_fresh_at cb x` by
    (qpat_assum `lower_value compile_expr ce _ off ca = _`
       (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] exprOperandVarTheory.compile_lower_value_var)) >>
     simp[]) >>
  qexists_tac `w` >> simp[] >> metis_tac[]
QED

Theorem blueprint_keyword_mono:
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  ca.cs_next_var <= cb.cs_next_var ==>
  local_ptrs_reserved ce cb /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cb x)
Proof
  metis_tac[local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono]
QED

Theorem blueprint_bind_success[local]:
  f p = (INL v,q) ==> bind f k p = k v q
Proof
  simp[bind_def]
QED

Theorem blueprint_eval_join_cons:
  bind (eval_expr cx e) (read_result cx) p = (INL v,q) /\
  eval_exprs cx es q = (INL vs,r) ==>
  eval_exprs cx (e::es) p = (INL (v::vs),r)
Proof
  strip_tac >> simp[eval_exprs_cons_action, GSYM bind_assoc, return_def] >>
  qpat_assum `bind _ _ p = (INL _,_)`
    (pure_once_rewrite_tac o single o MATCH_MP blueprint_bind_success) >>
  simp[bind_def, return_def]
QED

Theorem blueprint_optional_salt_at_cut:
  (hs ==> expr_body_pre ce cx env salt p /\ create_operand_completed_ok cx salt /\
      expr_type salt = BaseT (BytesT (Fixed 32))) /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_sim_inv ce cx env p /\
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
  (if hs then
      lower_value compile_expr ce (expr_type salt) salt ca = (op,cb) /\
      lower_value compile_expr (gas_shadow_env T ce) (expr_type salt) (gas_shadow_expr salt) sca = (op,scb) /\
      expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
      create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t /\
      t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts
   else cb = ca /\ scb = sca /\ t = u /\ chunk = []) /\
  (!vs. storage_trace_frame (k vs)) /\
  bind (eval_exprs cx (if hs then [salt] else [])) k p = (res,out) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?svs q G' tn'.
    eval_exprs cx (if hs then [salt] else []) p = (INL svs,q) /\ k svs q = (res,out) /\
    (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env q /\ ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
    return_buf_frame d ce cb t /\ alloca_history fnc t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx fnc t f i z ==> dalloca_fmp_headroom i z) /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted
Proof
  reverse (Cases_on `hs`) >> simp[cj 49 vyperInterpreterTheory.evaluate_def, return_def, bind_return] >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (disj2_tac >> qexistsl [`G`, `tn`] >> simp[] >> FIRST_ASSUM ACCEPT_TAC) >>
  `bind (bind (eval_expr cx salt) (read_result cx)) (\v. k [v]) p = (res,out)` by
    fs[create_copy_source_cons, cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  `!v. storage_trace_frame ((\v. k [v]) v)` by simp[] >>
  drule_all blueprint_read_at_cut >> strip_tac >- metis_tac[] >>
  `?w. dest_create_salt v = SOME w` by
    (irule blueprint_keyword_salt >> metis_tac[]) >>
  `eval_exprs cx [salt] p = (INL [v],q)` by
    (irule blueprint_eval_join_cons >> metis_tac[eval_exprs_nil]) >>
  disj2_tac >> qexistsl [`[v]`,`q`,`G'`,`tn'`] >> fs[] >> FIRST_ASSUM ACCEPT_TAC
QED

Theorem blueprint_eval_salt_offset:
  bind (eval_exprs cx ((if hs then [salt] else []) ++ [off])) k =
  bind (eval_exprs cx (if hs then [salt] else []))
    (\svs. bind (eval_exprs cx [off]) (\ovs. k (svs ++ ovs)))
Proof
  Cases_on `hs` >> simp[create_copy_source_cons, cj 49 vyperInterpreterTheory.evaluate_def, bind_return, ETA_AX]
QED

Theorem blueprint_eval_join_salt_offset:
  eval_exprs cx (if hs then [salt] else []) pa = (INL salts,ps) /\
  eval_exprs cx [off] ps = (INL [ov],qp) ==>
  eval_exprs cx ((if hs then [salt] else []) ++ [off]) pa = (INL (salts ++ [ov]),qp)
Proof
  strip_tac >>
  qabbrev_tac `act = eval_exprs cx ((if hs then [salt] else []) ++ [off])` >>
  `bind act return = act` by
    (simp[FUN_EQ_THM, bind_def, return_def] >> qx_gen_tac `s` >>
     Cases_on `act s` >> rename1 `act s = (rr,s')` >> Cases_on `rr` >> simp[]) >>
  `bind (eval_exprs cx ((if hs then [salt] else []) ++ [off])) return pa =
      (INL (salts ++ [ov]),qp)` by
    (pure_once_rewrite_tac[blueprint_eval_salt_offset] >> simp[bind_def, return_def]) >>
  qpat_x_assum `bind (eval_exprs cx _) return pa = _` mp_tac >>
  simp[Abbr `act`]
QED

Theorem blueprint_decoded_keywords:
  dest_AddressV av = SOME addr /\ dest_NumV amount = SOME value /\
  dest_NumV ov = SOME n /\
  (if hs then ?sv w. svs = [sv] /\ dest_create_salt sv = SOME w else svs = []) ==>
  ?ops. dest_create_args (CreateFromBlueprint raw) hs
      (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ amount::(svs ++ [ov])))) = SOME ops /\
    ops.co_code_src = AddressCodeSource addr /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME n
Proof
  Cases_on `hs` >> simp[] >> strip_tac >>
  gvs[create_operand_layout_def, dest_create_args_def, make_create_operands_def,
      dest_optional_num_def, dest_optional_salt_def, LENGTH_APPEND,
      DROP_PREFIX, TAKE_APPEND1]
QED

Theorem blueprint_eval_operand_frame:
  eval_operand op u = SOME aw /\ (!x. op = Var x ==> not_fresh_at ca x) /\
  (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
  t.vs_labels = u.vs_labels ==> eval_operand op t = SOME aw
Proof
  Cases_on `op` >> simp[eval_operand_def] >> metis_tac[]
QED
