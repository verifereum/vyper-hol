(* The two reached forced reads in flag membership. *)
Theory bodyMembershipFlagOperandsMods
Ancestors
  bodyBopBytestringBindMods bodyFullPostsMods bodyFullIfExpReach
  exprSimFullBundleProps exprBopSimProps bodyMemoryDefs bodyPtrDefs
  gasOutcomeFullPostPathMods gasOutcomeFullPostMods stmtSimForRounds
  exprSimDefs exprLoweringProps freshWrites loweringPosts vyperStorageTrace vyperStorageFootprint
  gasShadowState gasShadow compileEnv gasContext vyperState
Libs monadsyntax

(* A quotation for the linked landing post, with headroom at the same endpoint. *)
val flag_post = ``\e es sa sb s G tn op H v ee G' tn' t.
  expr_post_mods (H : (bool # 256 word # type_value) list # num list)
    ctx func cenv cx e es sa sb s ee v op t /\
  expr_store_bound cx (expr_type e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G' tn' t /\
  ptr_val_ok cx (post_value_type cenv e) v op G' tn' t /\
  ghost_kept_at lo cenv es sa G tn s G' tn' /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;

val flag_exit = ``\(H : (bool # 256 word # type_value) list # num list)
  (res : value + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;

val flag_entry = ``\es sa s G tn.
  local_ptrs_reserved cenv sa /\
  (!H : (bool # 256 word # type_value) list # num list. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts``;

Theorem flag_head_admissible[local]:
  gas_admissible (bind src next) expr_res_ok es ==>
  gas_admissible (src : evaluation_state -> value evaluation_result) expr_res_ok es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum irule >> qexistsl_tac [`ee`,`gs`] >> simp[bind_def]
QED

Theorem flag_operand_outcome[local]:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
  is_word_type (expr_type e) /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) sha = (op,shb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  ^flag_entry es sa s G tn /\
  (!H res ee gt r. ^flag_exit H res ee gt r ==> R H res ee gt r) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G' tn' t. ?v. res = INL v /\ ^flag_post e es sa sb s G tn op H v ee G' tn' t)
    (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r)
Proof
  BETA_TAC >> strip_tac >> fs[expr_sim_full_code_def] >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`sb`,`sha`,`shb`,`op`,`s`,`G`,`tn`] mp_tac o
     REWRITE_RULE[expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G' tn' t. childQ H res ee G' tn' t /\
     (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)`, `childR`] >>
  reverse (rpt conj_tac)
  >- (irule gas_outcome_full_mods_post_path >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[])
  >- (simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def] >>
      rpt strip_tac >> first_x_assum irule >> simp[]) >>
  simp[Abbr `childQ`] >> rpt strip_tac >> qexists_tac `v` >>
  simp[] >> first_assum ACCEPT_TAC
QED

val left_post = ``^flag_post e1 es sa s1 s0 G0 tn0 x``;
val right_post = ``\(v1 : value) mid G1 tn1 t. ^flag_post e2 mid s1 s2 t G1 tn1 y``;
val left_reached = ``\left v1 mid G1 tn1 t.
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
    (INL v1,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ mid.gas_obs = [] /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==> ^left_post H v1 mid G1 tn1 t)``;
val right_reached = ``\v1 mid G1 tn1 t right v2 fin G2 tn2 u.
  (!tail. bind (eval_expr cx e2) (read_result cx)
    (mid with gas_obs := gas_explicit right t.vs_gas_readings ++ tail) =
    (INL v2,fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\ ~u.vs_halted /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==> ^right_post v1 mid G1 tn1 t H v2 fin G2 tn2 u)``;
val flag_suffix = ``\v1 v2 ee. (bop_result cx ann bop [expr_type e1; expr_type e2] v1 v2 ee,ee)``;

Theorem membership_flag_operands_mods:
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  contract_inv mods exps ctx cenv cx /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e1) e1 es /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e1) (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,shadow_sa,shadow_s1) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,s2,shadow_s1,shadow_s2) /\
  sa.cs_next_var <= s1.cs_next_var /\
  gas_admissible (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx)) expr_res_ok es /\
  ^flag_entry es sa s0 G0 tn0 /\
  (!H res ee gt r. ^flag_exit H res ee gt r ==> R H res ee gt r) /\
  (!left v1 mid G1 tn1 t. ^left_reached left v1 mid G1 tn1 t ==>
      expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx (expr_type e1) e2 mid) /\
  (!left v1 mid G1 tn1 t right v2 fin G2 tn2 u.
    ^left_reached left v1 mid G1 tn1 t /\ ^right_reached v1 mid G1 tn1 t right v2 fin G2 tn2 u ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cenv.ce_modules cx st0 (^flag_suffix v1 v2) (fin,u,G2,tn2) Q R) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx (Builtin ann (Bop bop) [e1;e2])) (read_result cx))
    (es,s0,G0,tn0) Q R
Proof
  BETA_TAC >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     fs[expr_sim_full_code_def] >> qexists_tac `func` >> simp[]) >>
  qpat_x_assum `gas_admissible _ _ _`
    (assume_tac o PURE_REWRITE_RULE[REWRITE_RULE[ETA_AX] eval_expr_bop_bind]) >>
  pure_rewrite_tac[REWRITE_RULE[ETA_AX] eval_expr_bop_bind] >>
  drule_then assume_tac flag_head_admissible >>
  ho_match_mp_tac (GEN_ALL bop_bytestring_bind_mods) >>
  qexistsl_tac [`^right_post`,`^left_post`] >> BETA_TAC >>
  conj_tac
  >- (irule (BETA_RULE flag_operand_outcome) >>
      simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
      qexistsl_tac [`shadow_sa`,`shadow_func`,`shadow_s1`,`expr_type e1`] >> simp[]) >>
  conj_tac >- simp[storage_trace_frame_def,exprBopSimDefsTheory.bop_result_def] >>
  reverse conj_tac
  >- (pure_rewrite_tac[GSYM CONJ_ASSOC] >>
      first_assum (ACCEPT_TAC o REWRITE_RULE[GSYM CONJ_ASSOC])) >>
  qx_genl_tac [`left`,`v1`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr cx e1) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >> BETA_TAC >>
     disch_then (drule_then mp_tac) >> simp[] >>
     disch_then (ACCEPT_TAC o MATCH_MP flag_head_admissible)) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e2 mid` by
    (qpat_assum `!l v m g n t. _ ==> expr_sim_full_mods _ _ _ _ e2 _` irule >>
     conj_tac
     >- (qexistsl_tac [`G1`,`left`,`t`,`tn1`,`v1`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `return_buf_frame d cenv s1 t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[expr_post_mods_def,expr_post_def]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  irule (BETA_RULE flag_operand_outcome) >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then strip_assume_tac) >> fs[expr_post_mods_def,expr_post_def]) >>
  qexistsl_tac [`shadow_s1`,`shadow_func`,`shadow_s2`,`expr_type e1`] >> simp[]
QED
