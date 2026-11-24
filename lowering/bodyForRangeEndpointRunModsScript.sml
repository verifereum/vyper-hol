(* The checked Range endpoints and their actual landing frames. *)
Theory bodyForRangeEndpointRunMods
Ancestors
  bodyForRangeRouteMods bodyFullIfExpReach gasOutcomeFullPostMods
  bodyNormalHeadTailMods bodyBranchCellFrameMods exprBodyPreProps
  exprWordOperand exprSimSource exprSimProps bodyMemoryDefs exprLoweringProps
  stmtSimForRounds stmtSimDefs stmtSimProps gasContext loweringPosts
  vyperTypeInvariants vyperTypeExprSoundness vyperEvalPreservesScopes
  vyperStatePreservation fragGasOriginPtr finite_map compileEnv vyperTypeSystem
  bodyFullPredsMods bodyFullPostsMods exprSimHypsDefs bodySimDeclCases
  vyperState vyperInterpreter venomState fragExec bodyPtrDefs bodyFullShared
  gasOutcomeFullMods gasExplicitSites exprSimDefs stmtSimForRange
  vyperTypeExprResult vyperStorageTrace vyperStorageFootprint haltExitProj
  vyperValue valueEncoding bodySimFull loweringSlice vyperExprNoControl stmtFragPtr ptrDiscipline
Libs
  monadsyntax

val _ = Parse.hide "body";

Theorem range_int_word[local]:
  is_int_type typ ==> is_word_type typ
Proof
  Cases_on `typ` >> simp[is_int_type_def] >>
  rename1 `is_int_type (BaseT bt) ==> _` >> Cases_on `bt` >>
  simp[is_int_type_def,is_word_type_def]
QED

Theorem range_endpoint_val_sim[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx typ e es
Proof
  strip_tac >>
  qhdtm_x_assum `body_expr_full_ok_mods`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  qpat_assum `!df lo d pg src tops ctx sh fn shfn ce env ty es. _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
    (drule_all_then mp_tac) >> simp[IMP_CONJ_THM,FORALL_AND_THM] >>
  strip_tac >> first_assum (irule o SPEC_ALL)
QED

Theorem range_pre_gas_obs[local]:
  expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs) <=>
  expr_body_pre_mods mods cenv cx env e es
Proof
  simp[expr_body_pre_mods_def,expr_sim_inv_mods_def]
QED

Theorem range_inv_gas_obs[local]:
  expr_sim_inv_mods mods cenv cx env (es with gas_obs := gs) <=>
  expr_sim_inv_mods mods cenv cx env es
Proof
  simp[expr_sim_inv_mods_def]
QED

Theorem range_endpoint_read[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  is_int_type typ /\ expr_type e = typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (INL v,mid with gas_obs := tail) ==>
  expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid /\
  MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  ?n. v = IntV n /\ value_has_type tyv (IntV n)
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by
    simp[range_pre_gas_obs] >>
  drule_all_then strip_assume_tac (REWRITE_RULE [ETA_THM] body_range_endpoint_read_mods) >>
  drule_then (assume_tac o SRULE []) eval_read_preserves_scopes_dom >>
  `body_const_cells_agree_mods mods cx env (mid with gas_obs := tail)` by
    (drule_then (qx_choosel_then [`raw`,`m`] strip_assume_tac)
       (REWRITE_RULE [ETA_THM] eval_expr_read_INL) >>
     drule_then assume_tac read_result_state >>
     `?res. eval_stmt cx (Expr e) (es with gas_obs := gs) = (res,mid with gas_obs := tail)` by
       (gvs[] >> simp[Once evaluate_def,bind_def,type_check_def,assert_def,return_def,raise_def] >>
        Cases_on `is_HashMapRef raw` >> simp[]) >>
     `well_typed_expr env e` by (drule expr_body_pre_mods_well_typed >> simp[]) >>
     irule body_const_cells_agree_mods_stmt >>
     goal_assum (drule_at (Pat `eval_stmt _ _ _ = _`)) >>
     simp[type_stmt_def,well_typed_expr_not_hashmap_place]) >>
  fs[range_inv_gas_obs]
QED

Theorem range_endpoint_word_shape[local]:
  lower_value compile_expr cenv typ e sa = (op,sb) /\
  expr_body_pre_mods mods cenv cx env e es /\ is_word_type (expr_type e) ==>
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sb x) /\ (!l. op <> Label l)
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then (assume_tac) expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def,env_context_consistent_def] >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (simp[well_formed_type_def] >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC env_consistent_var_type_evaluates) >>
  drule_all_then strip_assume_tac lower_value_word_shape >> simp[]
QED

Theorem range_endpoint_operand[local]:
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee (IntV n) op t /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tyv ==>
  eval_operand op t = SOME (i2w n)
Proof
  simp[expr_post_mods_def,expr_post_def,expr_val_rel_def] >> strip_tac >>
  first_x_assum (qspec_then `tyv` mp_tac) >>
  simp[typed_val_to_w256_word_value,word_value_def,val_to_w256_def]
QED

Theorem range_endpoint_post_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q R /\
  (!marks H res ee G' tn' t.
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (s,G,tn) marks (OK t,G',tn') /\ storage_trace_domain cx st0 ee.storage_trace /\
    Q H res ee G' tn' t ==>
    Q' H res ee G' tn' t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 source
    (es,s,G,tn) Q' R
Proof
  strip_tac >>
  qhdtm_x_assum `gas_outcome_full_mods`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def]) >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      rpt conj_tac >- simp[] >- simp[] >>
      rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
      >- (disj1_tac >> first_x_assum irule >> simp[] >> qexists_tac `marks` >> simp[]) >>
      disj2_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem range_endpoint_admissible[local]:
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) next)
    (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `no_control_exc ex` by
    (qpat_assum `bind (eval_expr cx e) _ _ = _` mp_tac >>
     simp[NoAsms,bind_def,AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control,read_result_no_control]) >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def] >> Cases_on `ex` >> gvs[no_control_exc_def,expr_res_ok_def,stmt_res_ok_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[]
QED

Theorem range_endpoint_terminal[local]:
  expr_exit (res:value + exception) r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s) ==>
  ?ex. res = INR ex /\
    (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex : unit + exception) gt r) /\
    halt_exit H cx ee (INR ex : unit + exception) r /\
    (ctx_has_dalloca ctx ==> !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)
Proof
  strip_tac >> Cases_on `res` >- fs[expr_exit_INL] >> gvs[] >>
  conj_tac
  >- (simp[stmt_exit_ptr_def] >> gen_tac >> disj1_tac >>
      irule (iffLR (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``] expr_exit_INR_type)) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (irule (iffLR (INST_TYPE [alpha |-> ``:value``, beta |-> ``:unit``] halt_exit_INR_type)) >>
      first_assum ACCEPT_TAC) >>
  rpt strip_tac >- simp[] >>
  gvs[] >> rename1 `expr_exit (INR ex) (IntRet ir s)` >>
  Cases_on `ex` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >> gvs[expr_exit_def]
QED

(* Along a forced read, an output trace with a domain certifies its prefix. *)
Theorem range_endpoint_input_domain[local]:
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
    (res,ee with gas_obs := tail) /\ storage_trace_domain cx st0 ee.storage_trace ==>
  storage_trace_domain cx st0 es.storage_trace
Proof
  strip_tac >>
  qpat_assum `bind _ _ _ = _` (mp_then Any mp_tac
    (REWRITE_RULE [GSYM AND_IMP_INTRO] storage_trace_frame_prefix)) >>
  impl_tac >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result] >>
  simp[NoAsms] >> disch_then (qx_choose_then `obs` assume_tac) >>
  irule storage_trace_domain_prefix >> qexists_tac `obs` >> simp[GSYM AND_IMP_INTRO] >>
  first_x_assum (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC
QED

(* The linked post uses the endpoint's horizon. The anchor frame and ABI
   buffer separation are obtained using the prefix trace's own horizon. *)
Theorem range_endpoint_frame[local]:
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H'. valid_horizon cx st0 H' es.storage_trace ==> stmt_state_rel H' ctx func cenv cx es s0) /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sb.cs_next_var /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) ==>
  ret_pc_ok cenv sb t /\ return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
  alloca_frame cenv es sa s0 cenv ee t
Proof
  strip_tac >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (first_x_assum irule >> fs[storage_trace_domain_def]) >>
  fs[expr_post_mods_def,expr_post_def] >>
  conj_tac >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  conj_tac >- (irule (INST_TYPE [alpha |-> ``:256``] return_buf_sep_locals_kept) >>
    conj_tac >- fs[arithmeticTheory.ADD_COMM] >>
    qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >>
    qexists_tac `sa` >> simp[]) >>
  irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ es s0` (irule_at Any) >> simp[] >>
  first_assum ACCEPT_TAC
QED

(* A normally completed read at the end of its own paired interval. *)
Definition range_endpoint_landed_mods_def[nocompute]:
  range_endpoint_landed_mods (DF,lo,d,ctx,func) mods cx cenv env tyv e op sb
    (es,sa,s0,G0,tn0) H n ee G tn t <=>
    expr_post_mods H ctx func cenv cx e es sa sb s0 ee (IntV n) op t /\
    value_has_type tyv (IntV n) /\ eval_operand op t = SOME (i2w n) /\
    op_prov G op = NONE /\ op_taint tn op = {} /\
    expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
    MAP FDOM ee.scopes = MAP FDOM es.scopes /\ ee.gas_obs = [] /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ret_pc_ok cenv sb t /\ return_buf_frame d cenv sb t /\ return_buf_sep d cenv ee t /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t) /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_frame cenv es sa s0 cenv ee t
End

Theorem range_endpoint_linked_projection[local]:
  range_endpoint_landed_mods (DF,lo,d,ctx,func) mods cx cenv env tyv e op sb
    (es,sa,s0,G0,tn0) H n ee G tn t ==>
  stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
  storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t
Proof
  pure_rewrite_tac[range_endpoint_landed_mods_def,expr_post_mods_def,expr_post_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem range_endpoint_outcome[local]:
  cenv.ce_modules = mods /\
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  is_int_type typ /\ expr_type e = typ /\ evaluate_type (get_tenv cx) typ = SOME tyv /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx typ e es /\
  lower_value compile_expr cenv typ e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e) sha = (op,shb) /\
  gas_shadow_state sa sha /\ gas_shadow_state sb shb /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sha shb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\ gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ ?n. v = IntV n /\
      range_endpoint_landed_mods (DF,lo,d,ctx,func) mods cx cenv env tyv e op sb
        (es,sa,s0,G0,tn0) H n ee G tn t)
    (\H res ee gt r. ?ex. res = INR ex /\
      (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r) /\
      halt_exit H cx ee (INR ex : unit + exception) r /\
      (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  `is_word_type (expr_type e)` by (irule range_int_word >> simp[]) >>
  drule_all_then strip_assume_tac range_endpoint_word_shape >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`sha`,`shb`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_all_then assume_tac gas_outcome_full_mods_return_buf_allocas >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. ?v. _) _` kall_tac >>
  qpat_assum `cenv.ce_modules = mods` (fn eq =>
    qhdtm_x_assum `gas_outcome_full_mods` (assume_tac o REWRITE_RULE [eq])) >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ readQ readR` >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`\H res ee G tn t. readQ H res ee G tn t /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s)`, `readR`] >>
  rpt conj_tac
  >- suspend "normal"
  >- (simp[Abbr `readR`] >> rpt strip_tac >> irule range_endpoint_terminal >> simp[]) >>
  irule range_endpoint_post_path >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ readQ readR` (irule_at Any) >>
  simp[] >> rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]
QED

Resume range_endpoint_outcome[normal]:
  simp[Abbr `readQ`] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` (assume_tac o SRULE [])) >>
  drule_all_then strip_assume_tac range_endpoint_read >> gvs[] >>
  drule_all_then assume_tac range_endpoint_input_domain >>
  drule_all_then assume_tac range_endpoint_operand >>
  `!H'. valid_horizon cx st0 H' es.storage_trace ==> stmt_state_rel H' ctx func cenv cx es s0` by simp[] >>
  drule_all_then strip_assume_tac (SRULE [arithmeticTheory.ADD_COMM] range_endpoint_frame) >>
  fs[range_endpoint_landed_mods_def,ptr_val_ok_def,arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise range_endpoint_outcome

(* The original anchor sees the composition of two expression frames. *)
Theorem range_endpoint_frame_comp[local]:
  expr_post_mods H1 ctx func cenv cx e1 es sa m s0 mid1 (IntV n1) op1 t1 /\
  expr_post_mods H2 ctx func cenv cx e2 mid1 m z t1 mid2 (IntV n2) op2 t2 /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid1 m G1 tn1 t1 G2 tn2 /\
  alloca_frame cenv es sa s0 cenv mid1 t1 /\ alloca_frame cenv mid1 m t1 cenv mid2 t2 /\
  sa.cs_next_var <= m.cs_next_var /\ sa.cs_next_id <= m.cs_next_id ==>
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t2 = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t2.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\ op_taint tn2 (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv mid2 t2 /\
  (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!id b sz'. local_region cenv es.scopes s0 id b sz' ==> off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem)
Proof
  pure_rewrite_tac[expr_post_mods_def,expr_post_def,ghost_kept_at_def] >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at m x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> first_x_assum irule >> simp[]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> first_x_assum irule >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (gen_tac >> disch_tac >> rename1 `not_fresh_at sa x` >>
      `not_fresh_at m x` by simp[] >>
      qpat_assum `!y. not_fresh_at m y ==> _ /\ _` (drule_then strip_assume_tac) >>
      qpat_assum `!y. not_fresh_at sa y ==> _ /\ _` (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (irule alloca_frame_trans >> qpat_assum `alloca_frame cenv es sa s0 cenv mid1 t1` (irule_at Any) >>
      qexists_tac `m` >> simp[]) >>
  match_mp_tac (GEN_ALL alloca_taint_kept_trans) >>
  qpat_assum `alloca_frame cenv es sa s0 cenv mid1 t1` (irule_at Any) >>
  qexistsl_tac [`tn1`,`m`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem range_endpoint_saved_operand[local]:
  eval_operand op1 t1 = SOME w /\ op_prov G1 op1 = NONE /\ op_taint tn1 op1 = {} /\
  (!x. op1 = Var x ==> not_fresh_at m x) /\ (!l. op1 <> Label l) /\
  expr_post_mods H ctx func cenv cx e2 mid1 m z t1 mid2 v2 op2 t2 /\
  ghost_kept_at lo cenv mid1 m G1 tn1 t1 G2 tn2 ==>
  eval_operand op1 t2 = SOME w /\ op_prov G2 op1 = NONE /\ op_taint tn2 op1 = {}
Proof
  strip_tac >> conj_tac
  >- (irule range_first_operand_kept_mods >>
      qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]) >>
  Cases_on `op1` >> gvs[op_prov_def,op_taint_def,ghost_kept_at_def]
QED

(* Both replays can be chained with the observations of the next read as
   the first read's tail. No successful second read is needed to run e1. *)
Theorem range_checked_endpoints_ready_mods:
  cenv.ce_modules = mods /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_iterator_full_ok_mods mods exps cx (Range e1 e2) /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e1 es /\
  (!ee. expr_sim_inv_mods mods cenv cx env ee ==> expr_body_pre_mods mods cenv cx env e2 ee) /\
  is_int_type typ /\ expr_type e1 = typ /\ expr_type e2 = typ /\
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  lower_value compile_expr cenv typ e1 sa = (op1,m) /\
  lower_value compile_expr cenv typ e2 m = (op2,z) /\
  lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e1) sha = (op1,shm) /\
  lower_value compile_expr (gas_shadow_env T cenv) typ (gas_shadow_expr e2) shm = (op2,shz) /\
  gas_shadow_state sa sha /\ gas_shadow_state m shm /\ gas_shadow_state z shz /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa m func /\ fn_has_code m z func /\
  fn_has_code sha shm shadow_func /\ fn_has_code shm shz shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_stmt cx (For id typ (Range e1 e2) bound body)) (stmt_res_ok lctx) es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs1 gs2 n1 n2 mid1 mid2 G2 tn2 t2.
    (!tail. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs1 ++ tail) =
      (INL (IntV n1),mid1 with gas_obs := tail)) /\
    (!tail. bind (eval_expr cx e2) (read_result cx) (mid1 with gas_obs := gs2 ++ tail) =
      (INL (IntV n2),mid2 with gas_obs := tail)) /\
    value_has_type tyv (IntV n1) /\ value_has_type tyv (IntV n2) /\
    eval_operand op1 t2 = SOME (i2w n1) /\ eval_operand op2 t2 = SOME (i2w n2) /\
    op_prov G2 op1 = NONE /\ op_prov G2 op2 = NONE /\ op_taint tn2 op1 = {} /\ op_taint tn2 op2 = {} /\
    (!l. op1 <> Label l /\ op2 <> Label l) /\
    (!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at z x) /\
    sa.cs_next_var <= z.cs_next_var /\ sa.cs_next_id <= z.cs_next_id /\
    storage_trace_domain cx st0 mid2.storage_trace /\ mid2.gas_obs = [] /\
    expr_sim_inv_mods mods cenv cx env mid2 /\ body_const_cells_agree_mods mods cx env mid2 /\
    MAP FDOM mid2.scopes = MAP FDOM es.scopes /\
    ~t2.vs_halted /\ t2.vs_current_bb = z.cs_current_bb /\ t2.vs_inst_idx = LENGTH z.cs_current_insts /\
    local_ptrs_reserved cenv z /\ ret_pc_ok cenv z t2 /\ return_buf_frame d cenv z t2 /\
    return_buf_sep d cenv mid2 t2 /\ alloca_history func t2 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t2) /\ s0.vs_alloca_next <= t2.vs_alloca_next /\
    (!fn inst s. frag_reachable ctx func t2 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t2) /\
    (!H. valid_horizon cx st0 H mid2.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid2 t2 /\ immutable_frame_mods func cenv cx mid2 t2 /\
      storage_well_formed_on cx mid2 (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid2 G2 tn2 t2) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t2 = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t2.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G0 x /\ op_taint tn2 (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv mid2 t2 /\
    (!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!id b sz'. local_region cenv es.scopes s0 id b sz' ==> off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem) /\
    gas_admissible (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od)
      (stmt_res_ok lctx) mid2 ==>
    gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
      (do rl <- lift_sum (get_range_limits (IntV n1) (IntV n2));
        check (compatible_bound (Dynamic bound) (SND rl)) "For too long";
        eval_for cx tyv id body (GENLIST (\j. Value (IntV (FST rl + &j))) (SND rl)) od)
      (mid2,t2,G2,tn2) Q
      (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
        halt_exit H cx ee res r /\ (ctx_has_dalloca ctx ==>
          !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) mods cx st0
    (eval_stmt cx (For id typ (Range e1 e2) bound body)) (es,s0,G0,tn0) Q
    (\H res ee gt r. (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
      halt_exit H cx ee res r /\ (ctx_has_dalloca ctx ==>
        !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (match_mp_tac (GEN_ALL body_inv_no_phi_mods) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >> simp[]) >>
  `is_word_type typ` by (irule range_int_word >> simp[]) >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by simp[] >>
  `body_expr_full_ok_mods mods exps cx e1` by fs[body_iterator_full_ok_mods_def] >>
  drule_all_then assume_tac range_endpoint_val_sim >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME tyv`
    (fn ty => qpat_assum `gas_admissible (eval_stmt cx (For _ _ _ _ _)) _ es`
      (assume_tac o REWRITE_RULE [MATCH_MP eval_stmt_range_bind_mods ty])) >>
  irule range_full_endpoints_mods >>
  qexistsl_tac
    [`\H v ee G tn t. ?n. v = IntV n /\ range_endpoint_landed_mods (DF,lo,d,ctx,func)
                          mods cx cenv env tyv e1 op1 m (es,sa,s0,G0,tn0) H n ee G tn t`,
     `\v1 mid1 G1 tn1 t1 H v ee G tn t. ?n. v = IntV n /\
        range_endpoint_landed_mods (DF,lo,d,ctx,func) mods cx cenv env tyv e2 op2 z
          (mid1,m,t1,G1,tn1) H n ee G tn t`, `tyv`] >>
  BETA_TAC >> rpt conj_tac
  >- suspend "rest"
  >- first_assum ACCEPT_TAC >>
  suspend "first_read"
QED

Resume range_checked_endpoints_ready_mods[first_read]:
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    (irule range_endpoint_admissible >>
     qpat_assum `gas_admissible (bind (bind (eval_expr cx e1) _) _) _ es` (irule_at Any)) >>
  match_mp_tac (GEN_ALL range_endpoint_outcome) >>
  qexistsl_tac [`typ`,`shm`,`shadow_func`,`sha`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (irule o SPEC_ALL))
QED
Resume range_checked_endpoints_ready_mods[rest]:
  qx_genl_tac [`marks1`,`v1`,`mid1`,`G1`,`tn1`,`t1`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace) mid1.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _` (drule_then strip_assume_tac) >>
  `body_expr_full_ok_mods mods exps cx e2` by
    (irule range_iterator_second_mods >>
     qpat_assum `body_iterator_full_ok_mods _ _ _ _` (irule_at Any) >>
     qpat_assum `!tail. bind (eval_expr cx e1) _ _ = (INL v1,mid1 with gas_obs := tail)`
       (irule_at Any o SRULE [listTheory.APPEND_NIL] o Q.SPEC `[]`)) >>
  qhdtm_assum `range_endpoint_landed_mods`
    (strip_assume_tac o REWRITE_RULE [range_endpoint_landed_mods_def]) >>
  `expr_body_pre_mods mods cenv cx env e2 mid1` by simp[] >>
  drule_all_then assume_tac range_endpoint_val_sim >>
  `local_ptrs_reserved cenv m /\ sa.cs_next_var <= m.cs_next_var /\ sa.cs_next_id <= m.cs_next_id /\
   (!x. op1 = Var x ==> not_fresh_at m x) /\ (!l. op1 <> Label l)` by
    (qpat_assum `lower_value compile_expr cenv typ e1 sa = (op1,m)`
       (mp_then Any (drule_all_then strip_assume_tac) range_endpoint_word_shape) >>
     simp[] >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  qpat_assum `gas_admissible (bind (bind (eval_expr cx e1) _) _) _ es`
    (mp_then Any mp_tac (REWRITE_RULE [gas_admissible_gas_obs] gas_admissible_bind_tail)) >>
  disch_then (fn th => qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
    (mp_then Any (assume_tac o BETA_RULE) th)) >>
  conj_tac >- suspend "second_read" >>
  suspend "pair"
QED

Resume range_checked_endpoints_ready_mods[second_read]:
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok mid1` by
    (irule range_endpoint_admissible >>
     qpat_assum `gas_admissible (bind (bind (eval_expr cx e2) _) _) _ mid1` (irule_at Any)) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at m x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid1.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid1 t1 /\ immutable_frame_mods func cenv cx mid1 t1 /\
    storage_well_formed_on cx mid1 (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid1 G1 tn1 t1` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _` (drule_then strip_assume_tac) >>
     first_assum (ACCEPT_TAC o MATCH_MP range_endpoint_linked_projection)) >>
  match_mp_tac (GEN_ALL range_endpoint_outcome) >>
  qexistsl_tac [`typ`,`shz`,`shadow_func`,`shm`] >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE first_assum (irule o SPEC_ALL))
QED

Resume range_checked_endpoints_ready_mods[pair]:
  qx_genl_tac [`marks2`,`v2`,`mid2`,`G2`,`tn2`,`t2`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (drule_then (qx_choose_then `n2` strip_assume_tac)) >>
  rename1 `v1 = IntV n1` >>
  qpat_assum `range_endpoint_landed_mods _ _ _ _ _ _ e2 _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [range_endpoint_landed_mods_def]) >>
  qpat_assum `lower_value compile_expr cenv typ e2 m = (op2,z)`
    (mp_then Any (drule_all_then strip_assume_tac) range_endpoint_word_shape) >>
  qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ mid2 _ _ t2`
    (mp_then (Pat `expr_post_mods _ _ _ _ _ e2 _ _ _ _ mid2 _ _ t2`)
      (drule_all_then strip_assume_tac) range_endpoint_frame_comp) >>
  drule_all_then strip_assume_tac range_endpoint_saved_operand >>
  qpat_assum `gas_admissible (bind (bind (eval_expr cx e2) _) _) _ mid1`
    (mp_then Any mp_tac (REWRITE_RULE [gas_admissible_gas_obs] gas_admissible_bind_tail)) >>
  disch_then (fn th => qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
    (mp_then Any (assume_tac o BETA_RULE) th)) >>
  `sa.cs_next_var <= z.cs_next_var /\ sa.cs_next_id <= z.cs_next_id /\ s0.vs_alloca_next <= t2.vs_alloca_next`
    by decide_tac >>
  `local_ptrs_reserved cenv z` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `m` >> simp[]) >>
  `!x. op1 = Var x \/ op2 = Var x ==> not_fresh_at z x` by
    (rpt strip_tac >> simp[] >> irule not_fresh_at_mono >> qexists_tac `m` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid2 t2 /\ immutable_frame_mods func cenv cx mid2 t2 /\
    storage_well_formed_on cx mid2 (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx mid2 G2 tn2 t2` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _` (drule_then strip_assume_tac) >>
     first_assum (ACCEPT_TAC o MATCH_MP range_endpoint_linked_projection)) >>
  qpat_x_assum `v1 = IntV n1` SUBST_ALL_TAC >> qpat_x_assum `v2 = IntV n2` SUBST_ALL_TAC >>
  qpat_assum `!gs1 gs2 n1 n2 mid1 mid2 G2 tn2 t2. _` irule >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (qexistsl_tac [`gas_explicit marks1 s0.vs_gas_readings`,`gas_explicit marks2 t1.vs_gas_readings`,`mid1`] >> simp[]) ORELSE
   simp[arithmeticTheory.ADD_COMM])
QED
Finalise range_checked_endpoints_ready_mods
