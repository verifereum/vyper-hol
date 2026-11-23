(* Replay the keyword suffix without replaying the address or payload. *)
Theory entryCreateBlueprintSelectedKeywords
Ancestors
  entryCreateSelectedSalt createSizeBlueprintOffset entryCreateBlueprintReadCut
  createSizeBlueprintKeywordReplay createSizeOperandPre createSizeCopyReplay
  bodyFullPreds exprBodyPreProps exprOperandVar createSizePrefixReplay
  loweringPosts loweringStateRelDefs exprSimHypsDefs exprSimWordArgs vyperValue
  vyperTypeSystem vyperStorageFootprint vyperStorageTrace vyperState vyperCreate
  valueEncoding exprLoweringProps freshWrites arithmetic list compileEnv venomState

Theorem selected_offset_word[local]:
  value_runtime_typed env (BaseT (UintT 256)) v /\
  expr_val_rel cx (BaseT (UintT 256)) v op t ==>
  ?w. dest_NumV v = SOME (w2n w) /\ eval_operand op t = SOME w
Proof
  strip_tac >> drule blueprint_keyword_uint >> strip_tac >>
  gvs[expr_val_rel_def, evaluate_type_def, is_word_type_def,
      typed_val_to_w256_def, val_to_w256_def]
QED

Theorem blueprint_agreed_keywords_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env (Call ann (CreateTarget (CreateFromBlueprint raw) hs rof ks) args df) entry /\
  args = target::amount::((if hs then [salt] else []) ++ off::ctors) /\
  (!e p a b sha shb op u G tn.
    MEM e (create_operand_order (CreateFromBlueprint raw) hs args) /\
    body_const_cells_agree [(NONE,tops)] cx env p /\
    expr_body_pre ce cx env e p /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
      ce cx (expr_type e) e p (st0,a,b,sha,shb,op,u,G,tn) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
      tops cx st0 a b (bind (eval_expr cx e) (read_result cx)) (p,u,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,a,b,u,op,G,tn))) /\
  LENGTH cvs = LENGTH ctors /\ dest_AddressV av = SOME (w2w aw) /\
  eval_operand target_op u = SOME aw /\ (!x. target_op = Var x ==> not_fresh_at ca x) /\
  expr_sim_inv ce cx env p /\ body_const_cells_agree [(NONE,tops)] cx env p /\
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
    blueprint_literal_offset cx hs args = is_int_literal (origin_fold_value off) /\
    eval_operand target_op t = SOME aw /\ eval_operand offset_op t = SOME ow /\
    (!x. offset_op = Var x ==> not_fresh_at cb x) /\
    (lookup_account (w2w aw) q.accounts).code = (lookup_account (w2w aw) t.vs_accounts).code /\
    t.vs_labels = u.vs_labels /\ ca.cs_next_var <= cb.cs_next_var /\
    (!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type amount = BaseT (UintT 256) /\ expr_type off = BaseT (UintT 256) /\
   (hs ==> expr_type salt = BaseT (BytesT (Fixed 32)))` by
    (drule expr_body_pre_static_facts >> strip_tac >>
     Cases_on `hs` >> gvs[well_typed_expr_def, create_arg_types_ok_def]) >>
  `MEM amount args /\ MEM off args /\ (hs ==> MEM salt args)` by
    (Cases_on `hs` >> simp[]) >>
  `create_operand_order (CreateFromBlueprint raw) hs args =
    target::(ctors ++ amount::((if hs then [salt] else []) ++ [off]))` by
    (Cases_on `hs` >> simp[create_operand_order_def]) >>
  `MEM amount (create_operand_order (CreateFromBlueprint raw) hs args) /\
   MEM off (create_operand_order (CreateFromBlueprint raw) hs args) /\
   (hs ==> MEM salt (create_operand_order (CreateFromBlueprint raw) hs args))` by
    (Cases_on `hs` >> simp[MEM_APPEND]) >>
  qabbrev_tac `kfinal = \kvs. eval_create_operands cx (CreateFromBlueprint raw) hs rof
       (MAP expr_type args) (blueprint_literal_offset cx hs args) (av::(cvs ++ kvs))` >>
  `!kvs. storage_trace_frame (kfinal kvs)` by
    simp[Abbr `kfinal`, storage_trace_frame_create_operands] >>
  `expr_body_pre ce cx env amount p` by metis_tac[create_call_operand_body_pre] >>
  qabbrev_tac `ka = \v. bind (eval_exprs cx ((if hs then [salt] else []) ++ [off])) (\vs. kfinal (v::vs))` >>
  `bind (bind (eval_expr cx amount) (read_result cx)) ka p = (res,out)` by fs[Abbr `ka`, create_copy_source_cons] >>
  `!v. storage_trace_frame (ka v)` by simp[Abbr `ka`, blueprint_read_list_frame] >>
  suspend "amount"
QED

Resume blueprint_agreed_keywords_at_cuts[amount]:
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
     ce cx (expr_type amount) amount p (st0,ca,cm,sca,scm,amount_op,u,G,tn) ==>
   gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
     tops cx st0 ca cm (bind (eval_expr cx amount) (read_result cx)) (p,u,G,tn)
     (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx amount (p,ca,cm,u,amount_op,G,tn))` by
    (strip_tac >> first_assum irule >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`sca`,`scm`] >> first_assum ACCEPT_TAC) >>
  drule_all blueprint_read_at_cut_from_replay >>
  disch_then (strip_assume_tac o SPEC_ALL)
  >- metis_tac[] >>
  rename1 `bind (eval_expr cx amount) (read_result cx) p = (INL avalue,pa)` >>
  `body_const_cells_agree [(NONE,tops)] cx env pa` by
    (irule body_const_cells_agree_expr_read >> goal_assum (drule_at Any) >>
     qpat_assum `expr_body_pre ce cx env amount p`
       (strip_assume_tac o MATCH_MP expr_body_pre_static_facts) >> simp[]) >>
  drule_all blueprint_keyword_mono >> strip_tac >>
  `hs ==> expr_body_pre ce cx env salt pa` by metis_tac[create_call_operand_body_pre] >>
  qabbrev_tac `ksalt = \svs. bind (eval_exprs cx [off]) (\ovs. kfinal (avalue::(svs ++ ovs)))` >>
  `bind (eval_exprs cx (if hs then [salt] else [])) ksalt pa = (res,out)` by
    fs[Abbr `ka`, Abbr `ksalt`, blueprint_eval_salt_offset] >>
  `!svs. storage_trace_frame (ksalt svs)` by
    simp[Abbr `ksalt`, evaluate_storage_trace_frame, storage_trace_frame_bind_all] >>
  `m.vs_labels = u.vs_labels` by metis_tac[create_prefix_labels] >>
  suspend "salt"
QED

Resume blueprint_agreed_keywords_at_cuts[salt]:
  rename1 `ghost_inv_at (DF _) lo d ce cx pa Ga ta m` >>
  `hs ==> expr_body_pre ce cx env salt pa /\
    expr_type salt = BaseT (BytesT (Fixed 32)) /\
    (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
       ce cx (expr_type salt) salt pa (st0,cm,cn,scm,scn,salt_op,m,Ga,ta) ==>
     gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
       tops cx st0 cm cn (bind (eval_expr cx salt) (read_result cx)) (pa,m,Ga,ta)
       (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx salt (pa,cm,cn,m,salt_op,Ga,ta)))` by
    (strip_tac >> conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
     strip_tac >> first_assum irule >>
     rpt (conj_tac >- metis_tac[]) >> qexistsl [`scm`,`scn`] >> first_assum ACCEPT_TAC) >>
  drule_all blueprint_optional_salt_from_scalar >>
  disch_then (strip_assume_tac o SPEC_ALL)
  >- metis_tac[] >>
  rename1 `eval_exprs cx (if hs then [salt] else []) pa = (INL salts,ps)` >>
  `cm.cs_next_var <= cn.cs_next_var` by first_assum ACCEPT_TAC >>
  `local_ptrs_reserved ce cn /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cn x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cn x)` by
    (drule_all (Q.INST [`ca` |-> `cm`, `cb` |-> `cn`] blueprint_keyword_mono) >> simp[]) >>
  `n.vs_current_bb = cn.cs_current_bb /\
   n.vs_inst_idx = LENGTH cn.cs_current_insts /\ n.vs_labels = m.vs_labels` by
    (qpat_assum `if hs then lower_value _ _ _ salt cm = _ /\ _ else _` mp_tac >>
     Cases_on `hs` >> simp[] >> metis_tac[create_prefix_labels]) >>
  qabbrev_tac `ko = \ov. kfinal (avalue::(salts ++ [ov]))` >>
  `bind (bind (eval_expr cx off) (read_result cx)) ko ps = (res,out)` by
    fs[Abbr `ksalt`, Abbr `ko`, create_copy_source_cons,
       cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
  `!ov. storage_trace_frame (ko ov)` by simp[Abbr `ko`] >>
  drule_all create_blueprint_offset_bridge >> strip_tac >>
  suspend "offset"
QED

Resume blueprint_agreed_keywords_at_cuts[offset]:
  `(?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
   ?ov qp ow.
     bind (eval_expr cx off) (read_result cx) ps = (INL ov,qp) /\
     ko ov qp = (res,out) /\ dest_NumV ov = SOME (w2n ow) /\
     eval_operand offset_op t = SOME ow /\ stmt_state_rel H ctx fnc ce cx qp t /\
     (!x. offset_op = Var x ==> not_fresh_at cb x) /\
     cn.cs_next_var <= cb.cs_next_var /\ t.vs_labels = n.vs_labels /\
     (!x w. not_fresh_at cn x /\ lookup_var x n = SOME w ==> lookup_var x t = SOME w)`
  suffices_by (strip_tac >- metis_tac[] >> suspend "kfinal") >>
  qpat_x_assum `(?oty i. origin_fold_value off = _ /\ _) \/ _` strip_assume_tac
  >- suspend "folded" >>
  suspend "dynamic"
QED

Resume blueprint_agreed_keywords_at_cuts[folded]:
  first_assum (drule_then strip_assume_tac) >>
  `valid_horizon cx st0 H ps.storage_trace` by
    (qpat_assum `!ov. storage_trace_frame (ko ov)`
       (qspec_then `IntV i` assume_tac) >>
     `ko (IntV i) ps = (res,out)` by fs[bind_def] >>
     metis_tac[valid_horizon_frame]) >>
  disj2_tac >> qexistsl [`IntV i`,`ps`,`i2w i`] >>
  gvs[eval_operand_def, bind_def] >> metis_tac[]
QED

Resume blueprint_agreed_keywords_at_cuts[dynamic]:
  `expr_body_pre ce cx env off ps` by metis_tac[create_call_operand_body_pre] >>
  rename1 `ghost_inv_at (DF _) lo d ce cx ps Gs ts n` >>
  `expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc)
     ce cx (expr_type off) off ps (st0,cn,cb,scn,scb,offset_op,n,Gs,ts) ==>
   gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
     tops cx st0 cn cb (bind (eval_expr cx off) (read_result cx)) (ps,n,Gs,ts)
     (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx off (ps,cn,cb,n,offset_op,Gs,ts))` by
    (strip_tac >> first_assum irule >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`scn`,`scb`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full_pre _ _ _ _ amount _ _ ==> _` kall_tac >>
  drule_all blueprint_read_at_cut_from_replay >>
  disch_then (strip_assume_tac o SPEC_ALL)
  >- metis_tac[] >>
  `post_value_type ce off = BaseT (UintT 256)` by simp[is_word_type_def] >>
  `?ow. dest_NumV v = SOME (w2n ow) /\ eval_operand offset_op t = SOME ow` by
    (irule selected_offset_word >> metis_tac[]) >>
  `!x. offset_op = Var x ==> not_fresh_at cb x` by
    (qpat_assum `lower_value compile_expr ce _ off cn = _`
       (mp_tac o MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO] compile_lower_value_var)) >> simp[]) >>
  `t.vs_labels = n.vs_labels` by metis_tac[create_prefix_labels] >>
  disj2_tac >> qexistsl [`v`,`q`,`ow`] >> simp[] >> metis_tac[]
QED

Resume blueprint_agreed_keywords_at_cuts[kfinal]:
  `eval_exprs cx [off] ps = (INL [ov],qp)` by
    (irule blueprint_eval_join_cons >> metis_tac[eval_exprs_nil]) >>
  drule_all blueprint_eval_join_salt_offset >> strip_tac >>
  `?amt. dest_NumV avalue = SOME amt` by metis_tac[blueprint_keyword_uint] >>
  `?ops. dest_create_args (CreateFromBlueprint raw) hs
    (create_operand_layout (CreateFromBlueprint raw) hs (av::(cvs ++ avalue::(salts ++ [ov])))) = SOME ops /\
    ops.co_code_src = AddressCodeSource (w2w aw) /\ ops.co_ctor_args = cvs /\
    ops.co_code_offset = SOME (w2n ow)` by
    (irule blueprint_decoded_keywords >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (qexists_tac `amt` >> first_assum ACCEPT_TAC))) >>
  pop_assum strip_assume_tac >>
  `!x w. not_fresh_at ca x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w` by
    (rpt gen_tac >> strip_tac >>
     `not_fresh_at cm x /\ not_fresh_at cn x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono, LESS_EQ_TRANS] >>
     metis_tac[]) >>
  `t.vs_labels = u.vs_labels` by metis_tac[] >>
  `eval_operand target_op t = SOME aw` by
    (irule blueprint_eval_operand_frame >> qexistsl [`ca`,`u`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`avalue::(salts ++ [ov])`,`qp`,`ops`,`ow`] >>
  simp[] >> rpt conj_tac
  >- (irule blueprint_eval_join_cons >> qexists_tac `pa` >> simp[])
  >- (drule blueprint_lookup_code >> simp[]) >> decide_tac
QED
Finalise blueprint_agreed_keywords_at_cuts
