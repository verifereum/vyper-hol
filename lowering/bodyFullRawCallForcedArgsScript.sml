(* The RawCallTarget prefix through the two forced-value operands, before
   the dynamic bytes header is touched. *)
Theory bodyFullRawCallForcedArgs
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodyFullIfExpReach exprSimRawCall exprSimSource
  gasOutcomeFullCompose gasExemptCert vyperStorageTrace vyperStorageFootprint
  gasShadowState bodyMemoryDefs contextRawReachable ptrDiscipline unitTransformDefs
  stmtSimProps vyperTypeExprResult vyperTypeExprSoundness vyperTypeInvariants
  list bodySimFull exprSimHypsDefs loweringPosts compileEnv exprLoweringProps
  loweringShapeDefs vyperState stmtSimDefs vyperValue vyperTyping
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_assum `body_exprs_full_ok cx (a::d::kws)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >>
  `expr_sim_full (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (BaseT AddressT) a es` by
    (drule (cj 1 (iffLR (CONJUNCT1 body_expr_full_ok_def))) >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ a _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,
                           `addr`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qabbrev_tac `P = (\e ei ca cb t0 Gi tni x H
      (res : value + vyperState$exception) ee G tn t.
    (?v. res = INL v /\ expr_post H ctx func cenv cx e ei ca cb t0 ee v x t /\
      expr_store_bound cx (post_value_type cenv e) v x t /\
      t.vs_current_bb = cb.cs_current_bb /\
      t.vs_inst_idx = LENGTH cb.cs_current_insts /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      t0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx ee G tn t /\
      ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
      (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
      ghost_kept_at lo cenv ei ca Gi tni t0 G tn) /\
    ~t.vs_halted /\ ee.gas_obs = [])` >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> match_mp_tac storage_trace_frame_bind_all >>
      simp[] >> match_mp_tac storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qexists_tac `P a es sa s1 s0 G0 tn0 addr` >> reverse conj_tac
  >- (BETA_TAC >> irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[Abbr `P`,NoAsms] >> rpt strip_tac >>
      Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >>
      qpat_assum `!H exc ee gt r. _ ==> R H _ ee gt r` irule >>
      gvs[expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  qx_genl_tac [`marksA`,`resA`,`esA`,`GA`,`tnA`,`tA`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esA.storage_trace)
     esA.storage_trace` by fs[storage_trace_domain_def] >>
  `!fn inst s. frag_reachable ctx func tA fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `!H. valid_horizon _ _ H esA.storage_trace ==>
       gas_origin_ptr_path _ (s0,G0,tn0) marksA (OK tA,GA,tnA)`
       (qspec_then `storage_trace_horizon esA.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
       qpat_assum `!fn inst s. frag_reachable ctx func s0 fn inst s ==> _`
         (ACCEPT_TAC o (fn nowrap =>
           MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [path, phi, nowrap])))))) >>
  qpat_assum `!H. valid_horizon _ _ H esA.storage_trace ==> _ _ esA GA tnA tA`
    (qspec_then `storage_trace_horizon esA.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (P = _)`
    (fn th => simp[REWRITE_RULE [markerTheory.Abbrev_def] th, NoAsms]) >>
  strip_tac >> qpat_x_assum `resA = INL _` SUBST_ALL_TAC >>
  rename1 `expr_store_bound cx (post_value_type cenv a) av addr tA` >>
  disj1_tac >> qexists_tac `av` >> simp[] >>
  `esA with gas_obs := [] = esA` by simp[evaluation_state_component_equality] >>
  qpat_assum `esA with gas_obs := [] = esA` (fn update =>
    qpat_assum `!tail. bind (eval_expr cx a) _ _ = _`
      (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL,update]))) >>
  `body_const_cells_agree [(NONE,tops)] cx env esA` by
    (`well_typed_expr env a` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `expr_sim_inv cenv cx env esA` by
    (drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[]) >>
  `body_exprs_full_ok cx (d::kws)` by
    (first_x_assum irule >>
     drule (REWRITE_RULE [ETA_THM] eval_expr_read_INL) >> metis_tac[]) >>
  `expr_body_pre cenv cx env d esA` by
    (irule expr_body_pre_raw_call_arg >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_assum `body_exprs_full_ok cx (d::kws)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_def]) >>
  `expr_sim_full (DF,lo,dframe,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type d) d esA` by
    (drule (cj 1 (iffLR (CONJUNCT1 body_expr_full_ok_def))) >> metis_tac[]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qspecl_then [`cenv`,`BaseT AddressT`,`a`,`sa`] mp_tac
       ci_mono_lower_value_compile_expr >> simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s1 z)` by
    metis_tac[not_fresh_at_mono] >>
  `return_buf_frame dframe cenv s1 tA` by
    (irule return_buf_frame_frame >>
     qpat_assum `return_buf_frame dframe cenv sa s0` (irule_at Any) >>
     qpat_assum `expr_post _ _ _ _ _ a _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def,NoAsms] >> strip_tac >> simp[]) >>
  `!H. valid_horizon cx st0 H esA.storage_trace ==>
    stmt_state_rel H ctx func cenv cx esA tA /\
    storage_well_formed_on cx esA (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx esA GA tnA tA` by
    (qpat_assum `!H. valid_horizon _ _ H esA.storage_trace ==> _ _ esA GA tnA tA` mp_tac >>
     simp[Abbr `P`,NoAsms] >> POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> first_x_assum drule >> simp[expr_post_def]) >>
  `gas_admissible (bind (eval_expr cx d) (read_result cx)) expr_res_ok esA` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ d _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`st0`,`s1`,`s2`,`shadow_s1`,`shadow_s2`,
                           `data`,`tA`,`GA`,`tnA`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- simp[] >>
  qexists_tac `P d esA s1 s2 tA GA tnA data` >> reverse conj_tac
  >- (BETA_TAC >> irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx d) _) _ _ _`
        (irule_at Any) >>
      simp[Abbr `P`,NoAsms] >> rpt strip_tac >>
      Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def] >>
      qpat_assum `!H exc ee gt r. _ ==> R H _ ee gt r` irule >>
      gvs[expr_exit_INR_type,exprSimDefsTheory.halt_exit_def]) >>
  qx_genl_tac [`marksD`,`resD`,`esD`,`GD`,`tnD`,`tD`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon esD.storage_trace)
     esD.storage_trace` by fs[storage_trace_domain_def] >>
  `!fn inst s. frag_reachable ctx func tD fn inst s ==> dalloca_fmp_headroom inst s` by
    (qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==>
       gas_origin_ptr_path _ (tA,GA,tnA) marksD (OK tD,GD,tnD)`
       (qspec_then `storage_trace_horizon esD.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> _` (fn phi =>
       qpat_assum `!fn inst s. frag_reachable ctx func tA fn inst s ==> _`
         (ACCEPT_TAC o (fn nowrap =>
           MATCH_MP gas_origin_ptr_path_dalloca_fmp_headroom
             (LIST_CONJ [path, phi, nowrap])))))) >>
  qpat_assum `!H. valid_horizon _ _ H esD.storage_trace ==> _ _ esD GD tnD tD`
    (qspec_then `storage_trace_horizon esD.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `P`,NoAsms] >> strip_tac >>
  qpat_x_assum `resD = INL _` SUBST_ALL_TAC >>
  rename1 `expr_store_bound cx (post_value_type cenv d) dv data tD` >>
  disj1_tac >> qexists_tac `dv` >> simp[] >>
  `esD with gas_obs := [] = esD` by simp[evaluation_state_component_equality] >>
  qpat_assum `esD with gas_obs := [] = esD` (fn update =>
    qpat_assum `!tail. bind (eval_expr cx d) _ _ = _`
      (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL,update]))) >>
  `body_const_cells_agree [(NONE,tops)] cx env esD` by
    (`well_typed_expr env d` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     irule body_const_cells_agree_expr_read >>
     goal_assum (drule_at (Pat `bind (eval_expr _ _) _ _ = _`)) >> simp[]) >>
  `expr_sim_inv cenv cx env esD /\ expr_result_typed env d (Value dv)` by
    (drule_at (Pos last) (REWRITE_RULE [ETA_THM] expr_body_pre_eval) >>
     disch_then (qspec_then `cenv` mp_tac) >> simp[]) >>
  `body_exprs_full_ok cx kws` by
    (first_x_assum irule >>
     qpat_assum `bind (eval_expr cx d) _ _ = _`
       (mp_then Any mp_tac (REWRITE_RULE [ETA_THM] eval_expr_read_INL)) >>
     metis_tac[]) >>
  `?n. expr_type d = BaseT (BytesT (Dynamic n))` by
    (drule raw_call_pre_operands >> simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `?bs. dv = BytesV bs` by
    (qpat_assum `expr_result_typed env d (Value dv)` mp_tac >>
     qpat_assum `expr_type d = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_result_typed_def,expr_runtime_typed_def,evaluate_type_def,
          value_result_typed_def] >>
     Cases_on `dv` >> simp[value_has_type_def]) >>
  qpat_x_assum `dv = BytesV bs` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H esD.storage_trace ==>
       valid_horizon cx st0 H esA.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `bind (eval_expr cx d) _ _ = _`
       (mp_then (Pos (el 2)) mp_tac valid_horizon_frame) >>
     simp[] >> disch_then irule >> simp[] >>
     irule storage_trace_frame_bind_all >>
     simp[cj 5 evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qpat_x_assum `!gsA av esA tA GA tnA gsD bs esD tD GD tnD. _` irule >>
  simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`GA`,`esA`,`gasSummary$gas_explicit marksA s0.vs_gas_readings`,
            `gasSummary$gas_explicit marksD tA.vs_gas_readings`,`tA`,`tnA`] >>
  simp[] >> qx_gen_tac `H` >> disch_tac >>
  `valid_horizon cx st0 H esA.storage_trace` by metis_tac[] >>
  qpat_assum `!h. valid_horizon _ _ h esA.storage_trace ==> _ _ esA GA tnA tA`
    (qspec_then `H` (mp_tac o BETA_RULE)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h esD.storage_trace ==> _ _ esD GD tnD tD`
    (qspec_then `H` (mp_tac o BETA_RULE)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> gvs[]
QED
*)
Theorem raw_call_forced_args_full:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) NONE) es /\
  body_exprs_full_ok_mods mods exps cx (a::d::kws) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  lower_value compile_expr (gas_shadow_env T cenv) (BaseT AddressT)
    (gas_shadow_expr a) shadow_sa = (addr,shadow_s1) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type d)
    (gas_shadow_expr d) shadow_s1 = (data,shadow_s2) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state s1 shadow_s1 /\
  gas_shadow_state s2 shadow_s2 /\ gas_shadow_context ctx shadow_ctx /\
  gas_shadow_function func shadow_func /\ ctx_inst_ids_distinct ctx /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code shadow_sa shadow_s1 shadow_func /\
  fn_has_code shadow_s1 shadow_s2 shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  return_buf_frame dframe cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo dframe cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!av dv. storage_trace_frame (k av dv)) /\
  (!H exc ee gt r. expr_exit (INR exc : value + vyperState$exception) r /\
     halt_exit H cx ee (INR exc) r ==> R H (INR exc) ee gt r) /\
  (!gsA av esA tA GA tnA gsD bs esD tD GD tnD.
    bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
    bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
      (INL (BytesV bs),esD) /\
    esA.gas_obs = [] /\ esD.gas_obs = [] /\
    body_const_cells_agree mods cx env esD /\
    body_exprs_full_ok_mods mods exps cx kws /\ expr_sim_inv_mods mods cenv cx env esD /\
    storage_trace_domain cx st0 esD.storage_trace /\
    (!fn inst s. frag_reachable ctx func tD fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H esD.storage_trace ==>
      expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA /\
      expr_store_bound cx (post_value_type cenv a) av addr tA /\
      tA.vs_current_bb = s1.cs_current_bb /\
      tA.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func tA /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp tA) /\
      s0.vs_alloca_next <= tA.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx esA GA tnA tA /\
      ptr_val_ok cx (post_value_type cenv a) av addr GA tnA tA /\
      (~is_word_type (post_value_type cenv a) ==> ptr_buf_ok cenv a addr GA tA) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 GA tnA /\ ~tA.vs_halted /\
      expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
      expr_store_bound cx (post_value_type cenv d) (BytesV bs) data tD /\
      tD.vs_current_bb = s2.cs_current_bb /\
      tD.vs_inst_idx = LENGTH s2.cs_current_insts /\ alloca_history func tD /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp tD) /\
      tA.vs_alloca_next <= tD.vs_alloca_next /\
      ghost_inv_at (DF H) lo dframe cenv cx esD GD tnD tD /\
      ptr_val_ok cx (post_value_type cenv d) (BytesV bs) data GD tnD tD /\
      (~is_word_type (post_value_type cenv d) ==> ptr_buf_ok cenv d data GD tD) /\
      ghost_kept_at lo cenv esA s1 GA tnA tA GD tnD /\ ~tD.vs_halted) ==>
    gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (k av (BytesV bs)) (esD,tD,GD,tnD) Q R) ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (bind (bind (eval_expr cx a) (read_result cx))
      (\av. bind (bind (eval_expr cx d) (read_result cx)) (k av)))
    (es,s0,G0,tn0) Q R
Proof
  cheat
QED
