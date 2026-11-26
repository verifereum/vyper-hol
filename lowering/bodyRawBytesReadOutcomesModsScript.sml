(* Concrete linked forced reads at the raw byte-request entry and data cuts. *)
Theory bodyRawBytesReadOutcomesMods
Ancestors
  bodyRawRequestInputsMods bodyFullPostsMods bodyFullPredsMods
  bodyWriteSubscriptSourceMods bodyFullIfExpReach bodyMemoryDefs bodyBopBytestringPrepareMods
  gasOutcomeFullPostPathMods stmtSimForRounds
  exprSimFullBundleProps exprSimSliceCompose exprSimWordArgs exprOperandVar exprBodyPreProps
  exprLoweringProps loweringPosts vyperStorageFootprint vyperInterpreter vyperState list
Libs monadsyntax

val force = ``\e. bind (eval_expr cx e) (read_result cx)``;
val headroom = ``\t. !fn inst u. frag_reachable ctx func t fn inst u ==>
                                    dalloca_fmp_headroom inst u``;
val entry = ``\(es:evaluation_state) s G tn.
  !H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo dframe cenv cx es G tn s``;
val post = ``\e es sa sb s0 op G0 tn0 (H : (bool # 256 word # type_value) list # num list) v ee G tn t.
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo dframe cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val exit = ``\(H : (bool # 256 word # type_value) list # num list)
             (res:value + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val parent_pre = ``expr_body_pre_mods mods cenv cx env
  (Call ann (RawCallTarget flags) (a::data_expr::kws) NONE) es``;
val outcome = ``\action es s G tn Q.
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 action (es,s,G,tn) Q ^exit``;
val reached_post = ``\e es sa sb s0 op G0 tn0 H (res:value + exception) ee G tn t.
  ?v. res = INL v /\ ^post e es sa sb s0 op G0 tn0 H v ee G tn t /\ ^headroom t``;

Triviality read_outcome[local]:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  lower_value compile_expr cenv (expr_type e) e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) hsa = (op,hsb) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,hsa,hsb) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (^force e) expr_res_ok es /\
  return_buf_frame dframe cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\ (^headroom s0) /\
  (^entry es s0 G0 tn0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ^outcome (^force e) es s0 G0 tn0 (^reached_post e es sa sb s0 op G0 tn0)
Proof
  BETA_TAC >> strip_tac >> drule_then strip_assume_tac expr_sim_full_code_fields >>
  `expr_sim_full_mods (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (irule bop_bytestring_child_sim_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ e es` (irule_at Any) >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >> simp[] >>
     qexists_tac `exps` >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`sa`,`sb`,`hsa`,`hsb`,`op`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE[expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  irule gas_outcome_full_mods_post_path >>
  qhdtm_assum `gas_outcome_full_mods` (irule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi_mods >> disch_then (drule_then ACCEPT_TAC)) >>
  qexists_tac `v` >> simp[] >>
  qpat_assum `gas_origin_ptr_path _ _ _ (OK _,_,_)`
    (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
  qpat_assum `!fn inst u. frag_reachable ctx func s0 fn inst u ==> _`
    (pure_rewrite_tac o single o EQT_INTRO) >> simp[]
QED

Theorem raw_bytes_address_outcome_mods:
  ^parent_pre /\ body_exprs_full_ok_mods mods exps cx (a::data_expr::kws) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_type a = BaseT AddressT /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT) (gas_shadow_expr a) hsa = (addr,h1) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,s1,hsa,h1) /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (^force a) next) expr_vv_res_ok es /\
  return_buf_frame dframe cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\ (^headroom s0) /\
  (^entry es s0 G0 tn0) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ^outcome (^force a) es s0 G0 tn0 (^reached_post a es sa s1 s0 addr G0 tn0)
Proof
  BETA_TAC >> strip_tac >>
  drule_then assume_tac slice_gas_admissible_expr_head >>
  `expr_body_pre_mods mods cenv cx env a es` by
    (irule request_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
     simp[] >> drule expr_body_pre_mods_inv >> simp[]) >>
  `body_expr_full_ok_mods mods exps cx a` by fs[body_exprs_full_ok_mods_def] >>
  irule (Q.INST [`e` |-> `a`, `op` |-> `addr`, `sb` |-> `s1`] (BETA_RULE read_outcome)) >>
  qpat_assum `expr_body_pre_mods _ _ _ _ a es` (irule_at Any) >>
  qpat_assum `expr_sim_full_code _ _` (irule_at Any) >>
  qpat_assum `!fn inst u. frag_reachable ctx func s0 fn inst u ==> _`
    (pure_rewrite_tac o single o EQT_INTRO) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (strip_assume_tac o REWRITE_RULE [IMP_CONJ_THM]) >> simp[] >>
  qexistsl_tac [`tops`,`src`,`exps`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

val address_landed = ``
  (!tail. ^force a (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL av,esA with gas_obs := tail)) /\
  storage_trace_domain cx st0 esA.storage_trace /\ esA.gas_obs = [] /\ ~tA.vs_halted /\
  (!H. valid_horizon cx st0 H esA.storage_trace ==>
       ^post a es sa s1 s0 addr G0 tn0 H av esA GA tnA tA /\ ^headroom tA)``;
val data_static = ``^parent_pre /\ body_exprs_full_ok_mods mods exps cx (a::data_expr::kws) /\
  body_const_cells_agree_mods mods cx env es``;
val address_entry_resources = ``
  ci_mono sa s1 /\ local_ptrs_reserved cenv sa /\ return_buf_frame dframe cenv sa s0 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x)``;
val data_entry_resources = ``
  local_ptrs_reserved cenv s1 /\ return_buf_frame dframe cenv s1 tA /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
  tA.vs_current_bb = s1.cs_current_bb /\ tA.vs_inst_idx = LENGTH s1.cs_current_insts /\
  alloca_history func tA /\ (ctx_has_dalloca ctx ==> allocas_below_fmp tA) /\
  s0.vs_alloca_next <= tA.vs_alloca_next /\ ^headroom tA``;
val data_source = ``
  body_exprs_full_ok_mods mods exps cx (data_expr::kws) /\
  expr_body_pre_mods mods cenv cx env data_expr esA /\
  expr_sim_inv_mods mods cenv cx env esA /\ body_const_cells_agree_mods mods cx env esA``;

Triviality raw_bytes_data_source[local]:
  ^data_static /\ esA.gas_obs = [] /\
  (!tail. ^force a (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL av,esA with gas_obs := tail)) ==>
  ^data_source
Proof
  BETA_TAC >> strip_tac >>
  `expr_body_pre_mods mods cenv cx env a es` by
    (irule request_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
     simp[] >> drule expr_body_pre_mods_inv >> simp[]) >>
  `esA with gas_obs := [] = esA` by simp[evaluation_state_component_equality] >>
  qabbrev_tac `eo = es with gas_obs := gas_explicit marks s0.vs_gas_readings` >>
  `bind (eval_expr cx a) (read_result cx) eo = (INL av,esA)` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_assum `esA with gas_obs := [] = esA` (fn th => rewrite_tac[th]) >>
     simp[Abbr `eo`]) >>
  `expr_body_pre_mods mods cenv cx env a eo /\
   body_const_cells_agree_mods mods cx env eo` by simp[Abbr `eo`] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then strip_assume_tac
    (CONV_RULE (DEPTH_CONV ETA_CONV) exprSimSourceTheory.eval_expr_read_INL) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `body_exprs_full_ok_mods _ _ _ (a::_)`
        (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
      first_x_assum irule >> goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  irule request_operand_pre_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >> simp[]
QED

Theorem raw_bytes_data_reached_mods:
  ^data_static /\ ^address_landed /\ ^address_entry_resources ==>
  ^data_source /\ ^data_entry_resources /\ ^entry esA tA GA tnA
Proof
  BETA_TAC >> strip_tac >> conj_tac
  >- (irule (BETA_RULE raw_bytes_data_source) >>
      simp[] >>
      qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) es` (irule_at Any) >>
      qexistsl_tac [`s0`,`marks`,`av`] >> simp[]) >>
  reverse conj_tac
  >- (qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      fs[expr_post_mods_def,expr_post_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon esA.storage_trace) esA.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon esA.storage_trace` (drule_then strip_assume_tac)) >>
  fs[ci_mono_def] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame dframe cenv s1 tA` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     fs[expr_post_mods_def,expr_post_def]) >>
  simp[] >> rpt strip_tac >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]
QED

Theorem raw_bytes_data_outcome_mods:
  ^data_source /\ ^data_entry_resources /\ (^entry esA tA GA tnA) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\ ~tA.vs_halted /\
  expr_type data_expr = BaseT (BytesT (Dynamic cap)) /\
  lower_value compile_expr cenv (BaseT (BytesT (Dynamic cap))) data_expr s1 = (data,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT (BytesT (Dynamic cap)))
    (gas_shadow_expr data_expr) h1 = (data,h2) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (s1,s2,h1,h2) /\
  gas_admissible (bind (^force a) (\av. bind (^force data_expr) (suffix av))) expr_vv_res_ok es /\
  (!tail. ^force a (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
          (INL av,esA with gas_obs := tail)) /\ esA.gas_obs = [] ==>
  ^outcome (^force data_expr) esA tA GA tnA (^reached_post data_expr esA s1 s2 tA data GA tnA)
Proof
  BETA_TAC >> strip_tac >>
  `gas_admissible (bind (bind (eval_expr cx data_expr) (read_result cx)) (suffix av))
     expr_vv_res_ok esA` by
    (`esA with gas_obs := [] = esA` by simp[evaluation_state_component_equality] >>
     drule gas_admissible_bind_tail >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,`av`,`esA`] mp_tac) >>
     simp[]) >>
  drule_then assume_tac slice_gas_admissible_expr_head >>
  `body_expr_full_ok_mods mods exps cx data_expr` by fs[body_exprs_full_ok_mods_def] >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  `expr_sim_full_mods (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type data_expr) data_expr esA` by
    (irule bop_bytestring_child_sim_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ data_expr esA` (irule_at Any) >>
     qpat_assum `module_body_inv _ _ _ _ _` (irule_at Any) >> simp[] >>
     qexists_tac `exps` >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods`
    (qspecl_then [`st0`,`s1`,`s2`,`h1`,`h2`,`data`,`tA`,`GA`,`tnA`] mp_tac o
     REWRITE_RULE[expr_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[]))) >> strip_tac >>
  irule gas_outcome_full_mods_post_path >>
  qhdtm_assum `gas_outcome_full_mods` (irule_at Any) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (drule body_inv_no_phi_mods >> disch_then (drule_then ACCEPT_TAC)) >>
  qexists_tac `v` >> simp[] >>
  qpat_assum `gas_origin_ptr_path _ _ _ (OK _,_,_)`
    (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
  qpat_assum `!fn inst u. frag_reachable ctx func tA fn inst u ==> _`
    (pure_rewrite_tac o single o EQT_INTRO) >> simp[]
QED
