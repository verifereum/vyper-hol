(* Strict left-to-right EC operands, conditional only on the reached suffix. *)
Theory bodyECArithOperandsMods
Ancestors
  bodyECArithOperandReadyMods bodyECArithOperandCodeMods bodyECArithForceBindMods
  bodyECArithReadAdvanceMods bodyECArithStackReadCutMods
  bodyFullPredsMods bodyFullPostsMods bodyFullIfExpReach exprSimFullBundleProps
  bodyAggregateReadMods exprSimECArith exprLoweringProps
  bodyForcedStorageFrameMods vyperStorageTrace vyperStorageFootprint
  loweringShapeDefs loweringPosts compileEnv vyperState vyperContext bodyMemoryDefs
Libs monadsyntax

val parent = ``\e1 e2. Builtin a bt [e1;e2]``;
val forced = ``\e. bind (eval_expr cx e) (read_result cx)``;
val suffix = ``\e1 e2 v1 v2. ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2]``;
val code = ``\sa sb sha shb.
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,sha,shb)``;
val lower_pair = ``\e sa sb sha shb op.
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) sha = (op,shb)``;
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
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;
val cut = ``\e es sa sb s0 G0 tn0 op marks v ee t G tn.
  (!tail. ^forced e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
    expr_store_bound cx (post_value_type cenv e) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) /\
  (!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u)``;
val reach = ``\e es v ee.
  expr_sim_inv_mods mods cenv cx env ee /\ body_const_cells_agree_mods mods cx env ee /\
  value_runtime_typed env (expr_type e) v /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (?obs. ee.storage_trace = es.storage_trace ++ obs)``;
val qparent = ``\e sa sb s0 vv (H : (bool # 256 word # type_value) list # num list)
  (rr : eval_result + exception) ee G tn t.
  ?tv. rr = INL tv /\ vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
    ~is_bytestring_type (post_value_type cenv e) ==>
    vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
    (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx tv ee = (INL val, ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) /\
  (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
    ptr_buf_ok cenv e op G t) /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val rparent = ``\(H : (bool # 256 word # type_value) list # num list)
  (rr : eval_result + exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit rr r /\ halt_exit H cx ee rr r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;
val outcome = ``\(source : evaluation_state -> eval_result evaluation_result).
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 source``;
val reached_tail = ``
  !e1 e2 st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0 x y s1 s2 shadow_s1 shadow_s2 res shadow_res
    marks1 v1 es1 t1 G1 tn1 marks2 v2 es2 t2 G2 tn2.
    args = [e1;e2] /\ a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
    expr_type e1 = a /\ expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
    body_exprs_full_ok_mods mods exps cx [e1;e2] /\
    compile_expr cenv ty (^parent e1 e2) sa = (vv,sb) /\
    compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (^parent e1 e2))
      shadow_sa = (vv,shadow_sb) /\
    ^code sa sb shadow_sa shadow_sb /\ ^code sa s1 shadow_sa shadow_s1 /\
    ^code s1 s2 shadow_s1 shadow_s2 /\ ^code s2 sb shadow_s2 shadow_sb /\
    ^lower_pair e1 sa s1 shadow_sa shadow_s1 x /\ ^lower_pair e2 s1 s2 shadow_s1 shadow_s2 y /\
    (if bt = ECAdd then compile_ecadd_points x y else compile_ecmul_point x y) s2 = (res,sb) /\
    (if bt = ECAdd then compile_ecadd_points x y else compile_ecmul_point x y)
      shadow_s2 = (shadow_res,shadow_sb) /\ vv = FST (as_stack_val a (res,sb)) /\
    sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
    sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= s2.cs_next_id /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    gas_admissible (eval_expr cx (^parent e1 e2)) expr_vv_res_ok es /\
    ^entry es sa s0 G0 tn0 /\ ^entry es1 s1 t1 G1 tn1 /\ ^entry es2 s2 t2 G2 tn2 /\
    ^cut e1 es sa s1 s0 G0 tn0 x marks1 v1 es1 t1 G1 tn1 /\
    ^cut e2 es1 s1 s2 t1 G1 tn1 y marks2 v2 es2 t2 G2 tn2 /\
    ^reach e1 es v1 es1 /\ ^reach e2 es1 v2 es2 /\
    (!H. valid_horizon cx st0 H es2.storage_trace ==>
      valid_horizon cx st0 H es1.storage_trace /\ valid_horizon cx st0 H es.storage_trace) ==>
    ^outcome (^suffix e1 e2 v1 v2) (es2,t2,G2,tn2)
      (^qparent (^parent e1 e2) sa sb s0 vv) ^rparent``;

Theorem ec_arith_next_entry[local]:
  ^entry es sa s0 G0 tn0 /\ ^cut e es sa sb s0 G0 tn0 op marks v ee t G tn /\
  sa.cs_next_var <= sb.cs_next_var ==>
  ^entry ee sb t G tn
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    (qpat_assum `storage_trace_domain cx st0 ee.storage_trace` mp_tac >>
     simp_tac bool_ss [storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])
  >- (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
      fs[expr_post_mods_def,expr_post_def]) >>
  rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  fs[expr_post_mods_def,expr_post_def]
QED

Theorem ec_arith_head_sim[local]:
  body_exprs_full_ok_mods mods exps cx (e::rest) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env e es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  simp[Once body_exprs_full_ok_mods_def] >> strip_tac >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

Theorem ec_arith_from_tail_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin a bt args) es /\ ^reached_tail ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin a bt args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty (Builtin a bt args) es
Proof
  BETA_TAC >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_x_assum `!e1 e2 st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0 x y s1 s2 shadow_s1 shadow_s2 res shadow_res marks1 v1 es1 t1 G1 tn1 marks2 v2 es2 t2 G2 tn2. _`
    (mk_asm "tail") >>
  drule_all_then strip_assume_tac ec_arith_operand_ready_mods >>
  qpat_x_assum `args = _` SUBST_ALL_TAC >>
  `body_exprs_full_ok_mods mods exps cx [e1;e2]` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` strip_assume_tac >>
     fs[builtin_args_length_ok_def]) >>
  reverse conj_asm2_tac >- suspend "vv" >>
  irule materialized_value_from_vv_mods >> asm_rewrite_tac[] >> reverse conj_tac
  >- (rpt strip_tac >> drule eval_expr_builtin_value >> simp[]) >>
  asm_x "tail" kall_tac >>
  match_mp_tac ec_arith_stack_read_cut_mods >> fs[]
QED

Resume ec_arith_from_tail_mods[vv]:
  rewrite_tac[expr_vv_sim_full_mods_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  `^entry es sa s0 G0 tn0` by (BETA_TAC >> asm_rewrite_tac[]) >>
  drule_all_then (qx_choosel_then [`x`,`y`,`s1`,`s2`,`shadow_s1`,`shadow_s2`,`res`,`shadow_res`]
    strip_assume_tac) ec_arith_operand_code_mods >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule body_inv_no_phi_mods >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qexists_tac `func` >> simp[]) >>
  drule_all_then strip_assume_tac ec_arith_read_admissible_mods >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e1) e1 es` by
    (irule ec_arith_head_sim >> simp[] >> rpt (goal_assum (drule_at Any))) >>
  qpat_assum `bt = ECAdd \/ bt = ECMul` (fn opth =>
    pure_once_rewrite_tac[MATCH_MP ec_eval_bind opth]) >>
  irule ec_arith_force_bind_mods >> BETA_TAC >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame,ec_source_tail_storage_frame]) >>
  qexistsl_tac [`d`,`x`,`sa`,`s1`,`shadow_func`,`shadow_sa`,`shadow_s1`,`expr_type e1`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >> suspend "right"
QED

Resume ec_arith_from_tail_mods[right]:
  qx_genl_tac [`marks1`,`v1`,`es1`,`G1`,`tn1`,`t1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac ec_arith_read_advance_mods >>
  `expr_body_pre_mods mods cenv cx env e2 es1` by simp[] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e2) e2 es1` by
    (irule ec_arith_head_sim >> simp[] >> rpt (goal_assum (drule_at Any))) >>
  `^entry es1 s1 t1 G1 tn1` by
    (BETA_TAC >> match_mp_tac (Q.INST [`e` |-> `e1`, `marks` |-> `marks1`,
       `v` |-> `v1`, `op` |-> `x`] (BETA_RULE ec_arith_next_entry)) >> asm_rewrite_tac[]) >>
  pop_assum (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `gas_admissible (bind (eval_expr cx e2) (read_result cx)) expr_res_ok es1` by
    (first_x_assum irule >> asm_rewrite_tac[] >> goal_assum (drule_at Any)) >>
  irule ec_arith_force_bind_mods >> BETA_TAC >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- simp[ec_source_tail_storage_frame] >>
  qexistsl_tac [`d`,`y`,`s1`,`s2`,`shadow_func`,`shadow_s1`,`shadow_s2`,`expr_type e2`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >> suspend "suffix"
QED

Resume ec_arith_from_tail_mods[suffix]:
  qx_genl_tac [`marks2`,`v2`,`es2`,`G2`,`tn2`,`t2`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac (Q.INST [`e` |-> `e2`] ec_arith_read_advance_mods) >>
  `^entry es2 s2 t2 G2 tn2` by
    (BETA_TAC >> irule (BETA_RULE ec_arith_next_entry) >>
     rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
     qexistsl_tac [`G1`,`e2`,`es1`,`marks2`,`y`,`t1`,`s1`,`tn1`,`v2`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
       valid_horizon cx st0 H es1.storage_trace /\ valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     qpat_assum `es2.storage_trace = es1.storage_trace ++ _` (fn eq =>
       pop_assum (assume_tac o MATCH_MP gasOutcomeFullTheory.valid_horizon_append o
                  PURE_REWRITE_RULE [eq])) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `es1.storage_trace = es.storage_trace ++ _` (fn eq =>
       pop_assum (ACCEPT_TAC o MATCH_MP gasOutcomeFullTheory.valid_horizon_append o
                  PURE_REWRITE_RULE [eq]))) >>
  asm "tail" irule >> rpt (first_assum ACCEPT_TAC ORELSE conj_tac ORELSE REFL_TAC) >>
  qexistsl_tac [`G1`,`es1`,`marks1`,`marks2`,`res`,`s1`,`s2`,`shadow_res`,
                `shadow_s1`,`shadow_s2`,`shadow_sa`,`shadow_sb`,`t1`,`tn1`,`x`,`y`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac ORELSE goal_assum (drule_at Any))
QED

Finalise ec_arith_from_tail_mods
