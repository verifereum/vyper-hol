(* Run the base and then the forced index of a non-reading array subscript.
   The selector is supplied at the two actual child endpoints. *)
Theory bodyArrayNoCopyBindMods
Ancestors
  bodyArrayNoCopyCutsMods bodyFullPostsMods gasOutcomeFullMods gasOutcomeFullBindMods
  gasOutcomeFullPostMods gasExemptCertMods exprSimSubscriptArraySource
  haltExitProj exprSimDefs bodyMemoryDefs exprLoweringProps freshWrites
  gasContext gasShadow gasShadowState vyperInterpreter vyperState vyperAST
  vyperStorageTrace vyperStorageFootprint fragExec fragGasOriginPtr
  contextRawReachable venomState venomInst list stmtSimForRounds bodyFullIfExpReach bodyFullTargetSubscript

Theorem array_bind_keep_path[local]:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f (es,s,G,tn) Q R ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0 f (es,s,G,tn)
    (\H res ee G' tn' t. Q H res ee G' tn' t /\
      ?marks. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) marks (OK t,G',tn')) R
Proof
  rewrite_tac[gas_outcome_full_mods_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> simp[] >> rpt (goal_assum (drule_at Any)) >> simp[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      simp[] >> rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[] >>
      disj1_tac >> simp[] >> qexists_tac `marks` >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem array_key_bind_admissible[local]:
  gas_admissible (bind key next) expr_vv_res_ok mid ==>
  gas_admissible key expr_res_ok mid
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  simp[bind_def,expr_vv_res_ok_def,expr_res_ok_def]
QED

Theorem array_bind_horizon[local]:
  storage_trace_frame f /\ f (start with gas_obs := obs) = (res,ee) /\
  valid_horizon cx st0 H ee.storage_trace ==>
  valid_horizon cx st0 H start.storage_trace
Proof
  strip_tac >> qpat_assum `f _ = _` (mp_then (Pat `_ = _`) mp_tac valid_horizon_frame) >> simp[]
QED

Theorem array_bind_base_frame[local]:
  vv_post_mods H ctx func cenv cx obj es sa sm s0 mid raw bvv s ==>
  stmt_state_rel H ctx func cenv cx mid s /\ immutable_frame_mods func cenv cx mid s /\
  storage_well_formed_on cx mid (FST H) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x s = SOME w)
Proof
  simp[vv_post_mods_def]
QED

Theorem array_nocopy_children_bind_mods:
  ~subscript_reads_base cx obj idx /\ expr_type obj = ArrayT et bd /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  gas_admissible (eval_expr cx obj) expr_vv_res_ok es /\
  compile_expr cenv ty obj sa = (bvv,sm) /\
  lower_value compile_expr cenv ty idx sm = (iop,st2) /\
  compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr obj) shadow_sa = (bvv,shadow_sm) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr idx)
    shadow_sm = (iop,shadow_st2) /\
  loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
  compile_array_subscript (vv_operand bvv) iop
    (case bd of vyperAST$Fixed _ => F | vyperAST$Dynamic _ => T)
    (case bd of vyperAST$Fixed n => n | vyperAST$Dynamic _ => 0)
    (word_scale loc) (elem_size_in_location cenv loc et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_state st2 shadow_st2 /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code sa sm func /\ fn_has_code sm st2 func /\
  fn_has_code st2 sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_st2 shadow_func /\
  fn_has_code shadow_st2 shadow_sb shadow_func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty obj es /\
  (!obs raw mid. eval_expr cx obj (es with gas_obs := obs) = (INL raw,mid) ==>
     expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty idx mid) /\
  (!gs1 mid raw s G1 tn1 gs2 fin key it Gi tni.
    array_nocopy_cut_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty obj idx et bd st0
      (es,s0,G0,tn0) (sa,sm,st2,sb,bvv,iop,dst,loc)
      (shadow_sa,shadow_sm,shadow_st2,shadow_sb)
      (gs1,mid,raw,s,G1,tn1) (gs2,fin,key,it,Gi,tni) ==>
    array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func) cenv cx ann obj idx et bd st0
      (es,s0,G0,tn0) (sa,sb,dst,loc) (raw,key) (fin,it,Gi,tni)) ==>
  let e = Subscript ann obj idx; vv = LocatedValue ann (mk_ptr dst loc) in
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (eval_expr cx e) (es,s0,G0,tn0)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
           ~is_bytestring_type (post_value_type cenv e) ==>
           vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?v. read_result cx tv ee = (INL v,ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                  eval_operand (vv_operand vv) t = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                         val_in_memory rt v (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
               ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
               ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule eval_expr_subscript_bind >>
  disch_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  qhdtm_x_assum `expr_vv_sim_full_mods` (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> disch_then (assume_tac o MATCH_MP array_bind_keep_path) >>
  suspend "base_bind"
QED

Resume array_nocopy_children_bind_mods[base_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (eval_expr cx obj) _ baseQ baseR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_result >> goal_assum (drule_at Any) >> gvs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_select,storage_trace_frame_bind_all,
           evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "key_entry" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_expr _ _) _ baseQ baseR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `baseR`] >> gen_tac >> Cases >> simp[expr_exit_def]
QED

Resume array_nocopy_children_bind_mods[key_entry]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t1`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `baseQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >> rename1 `vv_post_mods _ _ _ _ _ _ _ _ _ _ mid raw bvv t1` >>
  qabbrev_tac `bobs = gas_explicit marks s0.vs_gas_readings` >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `eval_expr cx obj (es with gas_obs := bobs) = (INL raw,mid)` by
    (qpat_assum `!tail. eval_expr cx obj (es with gas_obs := _ ++ tail) = _`
       (qspec_then `[]` mp_tac) >> rewrite_tac[APPEND_NIL] >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,Abbr `bobs`]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty idx mid` by
    (qpat_assum `!obs raw mid. _ ==> expr_sim_full_mods _ _ _ _ _ _` drule >> simp[]) >>
  `gas_admissible (bind (bind (eval_expr cx idx) (read_result cx))
       (\v. select_result cx (expr_type obj) raw (ValueSubscript v))) expr_vv_res_ok mid` by
    (qpat_assum `gas_admissible (bind (eval_expr cx obj) _) _ es`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok mid` by
    (irule array_key_bind_admissible >>
     qexists_tac `\v. select_result cx (expr_type obj) raw (ValueSubscript v)` >>
     asm_rewrite_tac[]) >>
  suspend "key_run"
QED

Resume array_nocopy_children_bind_mods[key_run]:
  disj1_tac >> qexists_tac `raw` >> conj_tac >- REFL_TAC >>
  `!fn inst s. frag_reachable ctx func t1 fn inst s ==> dalloca_fmp_headroom inst s` by
    (match_mp_tac (GEN_ALL gas_origin_ptr_path_dalloca_fmp_headroom) >>
     qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) _ (OK t1,G1,tn1)` (irule_at Any) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac array_bind_base_frame >>
  `return_buf_frame d cenv sm t1` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`st2`,`shadow_sm`,`shadow_st2`,`iop`,`t1`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[] >> gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     drule_then strip_assume_tac array_bind_base_frame >> asm_rewrite_tac[])) >> strip_tac >>
  suspend "key_bind"
QED

Resume array_nocopy_children_bind_mods[key_bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ (bind (eval_expr cx idx) _) _ keyQ keyR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
      irule gas_exempt_cert_mods_bind_value >> goal_assum (drule_at Any) >> gvs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_select] >>
  qexists_tac `\H res ee G tn t. keyQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "select" >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ keyQ keyR` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `keyR`] >> rpt strip_tac >>
  Cases_on `res` >> fs[expr_exit_def] >> metis_tac[expr_exit_INR_retype,halt_exit_INR_type]
QED

Resume array_nocopy_children_bind_mods[select]:
  qx_genl_tac [`marks2`,`res`,`fin`,`Gi`,`tni`,`it`] >> BETA_TAC >> strip_tac >>
  qunabbrev_tac `keyQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >> rename1 `expr_store_bound _ _ key iop it` >>
  disj1_tac >> qexists_tac `key` >> conj_tac >- REFL_TAC >>
  qabbrev_tac `kobs = gas_explicit marks2 t1.vs_gas_readings` >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  `gas_admissible (select_result cx (expr_type obj) raw (ValueSubscript key)) expr_vv_res_ok fin` by
    (qpat_assum `gas_admissible (bind (bind (eval_expr _ _) _) _) _ _`
       (mp_then (Pat `gas_admissible _ _ _`) mp_tac gas_admissible_bind_tail) >>
     BETA_TAC >> disch_then (drule_then mp_tac) >> simp[]) >>
  `bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := kobs) = (INL key,fin)` by
    (qpat_assum `!tail. bind (eval_expr _ _) _ _ = _` (qspec_then `[]` mp_tac) >>
     rewrite_tac[APPEND_NIL] >>
     qpat_assum `fin with gas_obs := [] = fin` (fn th => rewrite_tac[th]) >>
     simp[NoAsms,Abbr `kobs`]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==> valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> disch_tac >>
     qpat_assum `eval_expr cx obj (es with gas_obs := bobs) = _`
       (mp_then (Pat `_ = _`) irule array_bind_horizon) >>
     simp[evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==> valid_horizon cx st0 H mid.storage_trace` by
    (gen_tac >> disch_tac >>
     qpat_assum `bind (eval_expr cx idx) _ (mid with gas_obs := kobs) = _`
       (mp_then (Pat `_ = _`) irule array_bind_horizon) >>
     simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  qpat_assum `!gs1 mid raw s G1 tn1 gs2 fin key it Gi tni. _ ==> _`
    (qspecl_then [`bobs`,`mid`,`raw`,`t1`,`G1`,`tn1`,`kobs`,`fin`,`key`,`it`,`Gi`,`tni`] mp_tac) >>
  simp[NoAsms,array_select_outcome_mods_def] >> impl_tac
  >- (rewrite_tac[array_nocopy_cut_mods_def] >>
      simp[GSYM CONJ_ASSOC, FORALL_AND_THM, RIGHT_FORALL_IMP_THM] >>
      conj_tac
      >- (qpat_assum `gas_admissible (select_result cx (expr_type obj) raw _) _ fin` mp_tac >>
          qpat_assum `expr_type obj = _` (fn th => rewrite_tac[th])) >>
      conj_tac
      >- (gen_tac >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
            (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (gen_tac >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
            (qspec_then `H` mp_tac) >>
          (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _ /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  simp[Abbr `baseR`]
QED

Finalise array_nocopy_children_bind_mods
