Theory entryCreateCopyAgreedReplay
Ancestors
  entryCreateFocusSpec createSizeCopyReplay createSizeOperandPre
  bodyInvCodeProps bodyFullPreds exprBodyPreProps exprSimFullBundleProps bodyFullIfExpReach
  exprLoweringProps exprOperandVar freshWrites s1PrefixDefs gasShadowCompileBase
  accountsRelProps stateRelProj exprSimHypsDefs exprSimSource bodyPtrDefs
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
  gasExplicitSites gasSummary exprLowering compileEnv builtinCreate vyperCreate list pair

(* Script-local notation for the shared read law's unchanged postcondition.
   This theorem uses the law conditionally so it need not import its proof. *)
Overload copy_read_result[local] = ``\tops cx ce env H st0 ctx fnc DF lo d
  e ca cb op u t k p res out rest tail.
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
      ghost_inv_at (DF h) lo d ce cx q G' tn' t) /\ ~t.vs_halted``

Overload copy_read_law[local] = ``\tops ctx ce cx shctx PG DF lo d fnc shfnc env st0 (ty:'a itself).
  !e p ca cb sca scb op u G tn chunk t k (res:'a + vyperState$exception) out H rest tail.
    body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
    expr_body_pre ce cx env e p /\
    (expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type e) e p
       (st0,ca,cb,sca,scb,op,u,G,tn) ==>
     gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,fnc,PG)
       tops cx st0 ca cb (bind (eval_expr cx e) (read_result cx)) (p,u,G,tn)
       (expr_sim_full_post (DF,lo,d,ctx,fnc) ce cx e (p,ca,cb,u,op,G,tn))) /\
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
    copy_read_result tops cx ce env H st0 ctx fnc DF lo d e ca cb op u t k p res out rest tail``

(* The entry facts threaded unchanged in shape through the real scalar cuts. *)
Overload copy_read_frame[local] = ``\DF lo d ctx fnc ce cx st0 ca p u G tn.
  local_ptrs_reserved ce ca /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ca x) /\
  return_buf_frame d ce ca u /\ alloca_history fnc u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (!f i z. frag_reachable ctx fnc u f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
      stmt_state_rel h ctx fnc ce cx p u /\ storage_well_formed_on cx p (FST h) /\
      ghost_inv_at (DF h) lo d ce cx p G tn u) /\
  ~u.vs_halted /\ u.vs_current_bb = ca.cs_current_bb /\ u.vs_inst_idx = LENGTH ca.cs_current_insts``

Overload copy_head_post[local] = ``\tops cx ce env DF lo d ctx fnc st0 H cb t xs k res out rest tail.
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v q G' tn'.
    bind (eval_exprs cx xs) (\vs. k (v::vs)) q = (res,out) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H q.storage_trace /\ expr_sim_inv ce cx env q /\
    body_const_cells_agree [(NONE,tops)] cx env q /\
    copy_read_frame DF lo d ctx fnc ce cx st0 cb q t G' tn'``

Theorem copy_agreed_list_head[local]:
  create_expr_prefix ca cb (gas_explicit_sites ctx shctx) ctx fnc u chunk t ==>
  bind (eval_exprs cx (e::xs)) k p = ((res:'a + vyperState$exception),out) ==>
  copy_read_law tops ctx ce cx shctx PG DF lo d fnc shfnc env st0 (:'a) /\
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ body_const_cells_agree [(NONE,tops)] cx env p /\
  expr_sim_scoped (DF,lo,d,ctx,shctx,PG,fnc,shfnc) ce cx (expr_type e) e p /\
  lower_value compile_expr ce (expr_type e) e ca = (op,cb) /\
  lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sca = (op,scb) /\
  expr_sim_full_code (ctx,shctx,fnc,shfnc) (ca,cb,sca,scb) /\
  (!h. dead_lo_ok h (DF h) lo ce cx) /\ copy_read_frame DF lo d ctx fnc ce cx st0 ca p u G tn /\
  t.vs_current_bb = cb.cs_current_bb /\ t.vs_inst_idx = LENGTH cb.cs_current_insts /\
  (!vs. storage_trace_frame (k vs)) /\
  valid_horizon cx st0 H out.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ rest) u.vs_gas_readings ++ tail ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v q G' tn'.
    bind (eval_exprs cx xs) (\vs. k (v::vs)) q = (res,out) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    valid_horizon cx st0 H q.storage_trace /\ expr_sim_inv ce cx env q /\
    body_const_cells_agree [(NONE,tops)] cx env q /\
    copy_read_frame DF lo d ctx fnc ce cx st0 cb q t G' tn'
Proof
  SIMP_TAC bool_ss [] >>
  disch_tac >> disch_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `bind (eval_exprs _ _) _ _ = _`
    (assume_tac o REWRITE_RULE [create_copy_source_cons]) >>
  qabbrev_tac `j = \v. bind (eval_exprs cx xs) (\vs. k (v::vs))` >>
  `!v. storage_trace_frame (j v)` by
    simp[Abbr `j`, storage_trace_frame_bind_all, evaluate_storage_trace_frame] >>
  `copy_read_result tops cx ce env H st0 ctx fnc DF lo d
     e ca cb op u t j p res out rest tail`
  by (CONV_TAC (REDEPTH_CONV BETA_CONV) >>
      last_x_assum (irule o CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
      qpat_assum `bind (bind _ _) j p = _` (irule_at Any) >>
      qpat_assum `create_expr_prefix ca cb _ _ _ u chunk t` (irule_at Any) >>
      qpat_assum `expr_sim_full_code _ (ca,cb,sca,scb)` (irule_at Any) >>
      simp[] >> qexistsl [`tn`,`G`] >> simp[] >>
      conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
      `cx_tops cx = tops` by (drule body_inv_main_code >> simp[]) >>
      `!bb. MEM bb fnc.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
        (fs[expr_sim_full_code_def] >> metis_tac[body_inv_no_phi]) >>
      drule_all expr_sim_scoped_completed >> simp[]) >>
  pop_assum (strip_assume_tac o BETA_RULE)
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env q` by
    (irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx e) _ p = _` (irule_at Any) >>
     drule expr_body_pre_static_facts >> simp[]) >>
  `ci_mono ca cb` by metis_tac[ci_mono_lower_value_compile_expr, SND] >>
  `local_ptrs_reserved ce cb` by (drule_all compiler_ci_mono_reserved >> simp[]) >>
  disj2_tac >> qexistsl [`v`,`q`,`G'`,`tn'`] >> gvs[Abbr `j`] >>
  conj_tac >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `ca` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem copy_source_action[local]:
  eval_expr cx (Call ann (CreateTarget CreateCopyOf hs rof ks) args dflt) =
  bind (eval_exprs cx args)
    (eval_create_operands cx CreateCopyOf hs rof (MAP expr_type args)
      (blueprint_literal_offset cx hs args))
Proof
  PURE_ONCE_REWRITE_TAC [evaluate_def] >> Cases_on `args` >>
  simp[create_operand_order_def, FUN_EQ_THM, bind_def]
QED

Theorem copy_accounts_from_row[local]:
  stmt_state_rel H ctx fnc ce cx q t /\ expr_sim_inv ce cx env q ==>
  ?acc. accounts_agree H cx.txn.target acc t.vs_accounts /\ accounts_well_typed acc
Proof
  strip_tac >>
  drule stmt_state_rel_state_rel >> disch_then (mp_tac o MATCH_MP state_rel_accounts) >>
  fs[expr_sim_inv_def] >> metis_tac[]
QED

Theorem copy_storage_gas[local,simp]:
  storage_well_formed_on cx (es with gas_obs := obs) r <=> storage_well_formed_on cx es r
Proof
  irule storage_well_formed_on_backends >> simp[]
QED

Theorem copy_ghost_gas[local,simp]:
  ghost_inv_at D lo d ce cx (es with gas_obs := obs) G tn s <=>
  ghost_inv_at D lo d ce cx es G tn s
Proof
  simp[ghost_inv_at_def]
QED

Theorem copy_salt_value[local]:
  compile_create_salt compile_expr ce (SOME e) a = (salt,b) /\
  compile_create_salt compile_expr (gas_shadow_env T ce) (SOME (gas_shadow_expr e)) sha = (salt,shb) ==>
  ?op. lower_value compile_expr ce (expr_type e) e a = (op,b) /\
       lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (op,shb)
Proof
  Cases_on `lower_value compile_expr ce (expr_type e) e a` >>
  Cases_on `lower_value compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha` >>
  simp[compile_create_salt_def, comp_bind_def, comp_return_def] >> metis_tac[optionTheory.SOME_11]
QED

(* Use the observed row and source equation to identify the actual cut.
   Match the shadow lowering before selecting the entry ghosts. *)
fun copy_head_at path source shadow_lowering (tn, g) =
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> irule copy_agreed_list_head >>
  qpat_assum path (irule_at Any) >>
  qpat_assum source (irule_at Any) >>
  qpat_assum shadow_lowering (irule_at Any) >>
  qexistsl [tn, `shadow_func`, `PG`, g] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
  simp[expr_sim_full_code_def]

fun copy_accounts_at trace =
  disj2_tac >>
  qpat_assum trace (qspec_then `H` (drule_then strip_assume_tac)) >>
  drule_all copy_accounts_from_row >> simp[]

Theorem copy_agreed_accounts_at_cuts:
  has_salt = IS_SOME salt_e /\
  args = target_e::value_e::(case salt_e of NONE => [] | SOME e => [e]) /\
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  expr_body_pre cenv cx env (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,(PG : (num # num) option list),func,shadow_func)
    cenv cx ty (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt) es
    (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) /\
  (!e p. MEM e args /\ expr_body_pre cenv cx env e p /\
    body_const_cells_agree [(NONE,tops)] cx env p ==>
    expr_sim_scoped (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e) e p) /\
  copy_read_law tops ctx cenv cx shadow_ctx PG DF lo d func shadow_func env st0 (:eval_result) /\
  lower_value compile_expr cenv (expr_type target_e) target_e sa = (target,a1) /\
  lower_value compile_expr cenv (expr_type value_e) value_e a1 = (value,a2) /\
  compile_create_salt compile_expr cenv salt_e a2 = (salt,a3) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type target_e) (gas_shadow_expr target_e) shadow_sa = (target,b1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type value_e) (gas_shadow_expr value_e) b1 = (value,b2) /\
  compile_create_salt compile_expr (gas_shadow_env T cenv) (OPTION_MAP gas_shadow_expr salt_e) b2 = (salt,b3) /\
  gas_shadow_state a1 b1 /\ gas_shadow_state a2 b2 /\ gas_shadow_state a3 b3 /\
  fn_has_code sa a1 func /\ fn_has_code a1 a2 func /\ fn_has_code a2 a3 func /\
  fn_has_code shadow_sa b1 shadow_func /\ fn_has_code b1 b2 shadow_func /\ fn_has_code b2 b3 shadow_func /\
  create_expr_prefix sa a1 (gas_explicit_sites ctx shadow_ctx) ctx func s0 m1 u1 /\
  create_expr_prefix a1 a2 (gas_explicit_sites ctx shadow_ctx) ctx func u1 m2 u2 /\
  create_expr_prefix a2 a3 (gas_explicit_sites ctx shadow_ctx) ctx func u2 m3 u3 /\
  u1.vs_current_bb = a1.cs_current_bb /\ u1.vs_inst_idx = LENGTH a1.cs_current_insts /\
  u2.vs_current_bb = a2.cs_current_bb /\ u2.vs_inst_idx = LENGTH a2.cs_current_insts /\
  u3.vs_current_bb = a3.cs_current_bb /\ u3.vs_inst_idx = LENGTH a3.cs_current_insts /\
  eval_expr cx (Call ann (CreateTarget CreateCopyOf has_salt rof ks) args dflt)
    (es with gas_obs := gas_explicit (m1 ++ (m2 ++ (m3 ++ mr))) s0.vs_gas_readings ++ tail) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  (?acc. accounts_agree H cx.txn.target acc u3.vs_accounts /\ accounts_well_typed acc)
Proof
  SIMP_TAC bool_ss [] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[expr_vv_sim_full_pre_def]) >>
  `!e p. MEM e args /\ expr_sim_inv cenv cx env p ==> expr_body_pre cenv cx env e p` by
    (rpt strip_tac >> irule create_call_operand_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) es` (irule_at Any) >> simp[]) >>
  `expr_sim_inv cenv cx env es` by (drule expr_body_pre_static_facts >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` (assume_tac o REWRITE_RULE[copy_source_action]) >>
  qmatch_asmsub_abbrev_tac `bind (eval_exprs cx args) k p` >>
  `!vs. storage_trace_frame (k vs)` by simp[Abbr `k`, storage_trace_frame_create_operands] >>
  `p.gas_obs = gas_explicit (m1 ++ (m2 ++ (m3 ++ mr))) s0.vs_gas_readings ++ tail /\
   p.storage_trace = es.storage_trace /\
   body_const_cells_agree [(NONE,tops)] cx env p /\ expr_sim_inv cenv cx env p` by simp[Abbr `p`] >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  `copy_head_post tops cx cenv env DF lo d ctx func st0 H a1 u1
     (value_e::(case salt_e of NONE => [] | SOME e => [e])) k res ee (m2 ++ (m3 ++ mr)) tail` by
    (copy_head_at `create_expr_prefix sa a1 _ _ _ s0 m1 u1`
       `bind (eval_exprs cx (target_e::_)) k p = _`
       `lower_value _ _ _ (gas_shadow_expr target_e) shadow_sa = _` (`tn0`,`G0`) >>
     simp[Abbr `p`] >> qx_gen_tac `h` >> disch_tac >>
     qpat_assum `!h. valid_horizon _ _ h es.storage_trace ==> _` (qspec_then `h` mp_tac) >> simp[]) >>
  pop_assum (strip_assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV))
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  rename1 `ghost_inv_at (DF _) lo d cenv cx p1 G1 tn1 u1` >>
  qmatch_asmsub_abbrev_tac `bind (eval_exprs cx (value_e::_)) k1 p1` >>
  `!vs. storage_trace_frame (k1 vs)` by simp[Abbr `k1`] >>
  `copy_head_post tops cx cenv env DF lo d ctx func st0 H a2 u2
     (case salt_e of NONE => [] | SOME e => [e]) k1 res ee (m3 ++ mr) tail` by
    copy_head_at `create_expr_prefix a1 a2 _ _ _ u1 m2 u2`
      `bind (eval_exprs cx (value_e::_)) k1 p1 = _`
      `lower_value _ _ _ (gas_shadow_expr value_e) b1 = _` (`tn1`,`G1`) >>
  pop_assum (strip_assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV))
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  rename1 `ghost_inv_at (DF _) lo d cenv cx p2 G2 tn2 u2` >>
  Cases_on `salt_e`
  >- (gvs[compile_create_salt_def, comp_return_def] >>
      drule_all create_copy_empty_cut >> strip_tac >>
      qpat_x_assum `u3 = u2` SUBST_ALL_TAC >>
      copy_accounts_at `!h. valid_horizon _ _ h p2.storage_trace ==> _`) >>
  rename1 `compile_create_salt _ _ (SOME se) a2 = _` >>
  qpat_x_assum `compile_create_salt _ _ (OPTION_MAP _ (SOME _)) _ = _`
    (assume_tac o SIMP_RULE std_ss [optionTheory.OPTION_MAP_DEF]) >>
  drule_all copy_salt_value >> strip_tac >>
  qpat_x_assum `bind (eval_exprs cx (case SOME se of _ => _ | _ => _)) _ p2 = _`
    (assume_tac o SIMP_RULE std_ss [optionTheory.option_case_def]) >>
  qmatch_asmsub_abbrev_tac `bind (eval_exprs cx [se]) k2 p2` >>
  `!vs. storage_trace_frame (k2 vs)` by simp[Abbr `k2`] >>
  rename1 `lower_value compile_expr cenv (expr_type se) se a2 = (salt_op,a3)` >>
  `copy_head_post tops cx cenv env DF lo d ctx func st0 H a3 u3 [] k2 res ee mr tail` by
    copy_head_at `create_expr_prefix a2 a3 _ _ _ u2 m3 u3`
      `bind (eval_exprs cx [se]) k2 p2 = _`
      `lower_value _ _ _ (gas_shadow_expr se) b2 = _` (`tn2`,`G2`) >>
  pop_assum (strip_assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV))
  >- (disj1_tac >> goal_assum drule >> simp[]) >>
  rename1 `ghost_inv_at (DF _) lo d cenv cx p3 G3 tn3 u3` >>
  copy_accounts_at `!h. valid_horizon _ _ h p3.storage_trace ==> _`
QED
