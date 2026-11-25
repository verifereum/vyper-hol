(* Keep the staging width on the same raw expression run as the forced read. *)
Theory bodyAssignNameCopyReadFrontierMods
Ancestors
  bodyAssignNameLinkedSetup bodyLocalCopyPhysicalRhsMods bodyFullPostsMods
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  exprSimMemorySource exprSimUnwrap haltExitProj stmtSimProps valueCopyBytes
  gasShadowCompileBase vyperStorageTrace vyperStorageFootprint vyperState
  context loweringPosts compileEnv exprLowering exprSimDefs fragExec fragGasOriginPtr vyperAST
Libs monadsyntax

val read_post = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : value + vyperState$exception) ee G tn t.
  ?v. res = INL v /\
  expr_post_mods H ctx func cenv cx e es sa sb s0 ee v opr t /\
  expr_store_bound cx (post_value_type cenv e) v opr t /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v opr G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e opr G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;
val read_capacity = ``\t. !rt w.
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
  eval_operand opr t = SOME w ==>
  type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next``;
val read_guard = ``is_bytestring_type ty /\ vv_location vv = SOME LocMemory``;
val read_plus = ``\H res ee G tn t. ^read_post H res ee G tn t /\
  ee.gas_obs = [] /\ ~t.vs_halted /\ (^read_guard ==> ^read_capacity t)``;
val raw_post = ``\(H : (bool # 256 word # type_value) list # num list)
    (res : eval_result + vyperState$exception) ee G tn t.
  ee.gas_obs = [] /\ ~t.vs_halted /\
  ?tv. res = INL tv /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
  t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
  (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand G t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn``;

Theorem staged_copy_read_witness[local]:
  vv_location vv = SOME LocMemory /\ ~is_word_type (post_value_type cenv e) /\
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
  unwrap_value cenv vv sm = (opr,sb) ==>
  ?t' p v. vv = LocatedValue t' p /\ p.ptr_location = LocMemory /\
    ~is_word_type t' /\ p.ptr_operand = opr /\ read_result cx tv ee = (INL v,ee)
Proof
  Cases_on `vv` >> simp[vv_location_def] >> strip_tac >>
  `vv_holds_mods cenv cx (post_value_type cenv e) tv (LocatedValue t' p) ee t` by
    fs[vv_post_mods_def] >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_mods_def, vv_holds_def] >> strip_tac >>
  `~is_word_type t'` by metis_tac[is_bytestring_word_type] >>
  gvs[unwrap_value_def, comp_return_def]
QED

Theorem staged_copy_read_outcome:
  vv_location vv = SOME LocMemory /\ ~is_word_type (post_value_type cenv e) /\
  unwrap_value cenv vv sm = (opr,sb) /\
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0 (eval_expr cx e)
    (es,s0,G0,tn0) ^raw_post (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0) ^read_plus (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `^raw_post` >> BETA_TAC >> reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume staged_copy_read_outcome[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >> gvs[] >>
  `vv_post_mods (storage_trace_horizon ee.storage_trace) ctx func cenv cx e es sa sm s0 ee tv vv t` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  drule_all_then (qx_choosel_then [`src_ty`,`p`,`v`] strip_assume_tac) staged_copy_read_witness >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G`,`ee`,`INL v`,`t`,`tn`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `vv_post_mods (storage_trace_horizon _) _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> simp[] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `sb = sm /\
   gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (t,G,tn) [] (OK t,G,tn) /\
   expr_post_mods H ctx func cenv cx e es sa sb s0 ee v opr t /\
   ptr_val_ok cx (post_value_type cenv e) v opr G tn t /\
   expr_store_bound cx (post_value_type cenv e) v opr t /\ ^read_capacity t` by
    (BETA_TAC >> irule local_copy_rhs_identity_unwrap_mods >> simp[] >>
     qexistsl_tac [`tv`,`LocatedValue src_ty p`] >> simp[]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Finalise staged_copy_read_outcome[local]

Theorem copy_read_post_nonword[local]:
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e) ==>
  ~is_word_type (post_value_type cenv e)
Proof
  Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[post_value_type_def, expr_type_def] >> IF_CASES_TAC >> simp[]) >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_not_int_call >> metis_tac[]) >> simp[]
QED

Theorem assign_name_copy_read_frontier_mods:
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type cenv e) /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (opr,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa = (opr,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv.ce_modules cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ^read_plus H res ee G tn t /\
      (!bw cap. d = SOME (bw,cap) ==> allocas_from (w2n bw + cap) t)) (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  BETA_TAC >> ho_match_mp_tac gas_outcome_full_mods_return_buf_allocas >>
  reverse conj_tac >- simp[] >>
  Cases_on `^read_guard`
  >- suspend "staged" >>
  `lower_value compile_expr cenv (expr_type e) e sa = (opr,sb)` by
    simp[lower_value_def, comp_bind_def] >>
  qpat_assum `expr_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`opr`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disch_tac >> irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >> simp[]
QED

Resume assign_name_copy_read_frontier_mods[staged]:
  drule_all_then assume_tac copy_read_post_nonword >>
  drule_all_then (qx_choose_then `shadow_sm` strip_assume_tac) assign_name_shadow_raw_rhs_mods >>
  `unwrap_value cenv vv shadow_sm = (opr,shadow_sb)` by
    (qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     simp[lower_value_def, comp_bind_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    (qpat_assum `compile_expr _ _ e sa = _` (strip_assume_tac o MATCH_MP compile_expr_extends) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (strip_assume_tac o MATCH_MP compile_expr_extends) >>
     qpat_assum `unwrap_value _ _ sm = _` (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
     qpat_assum `unwrap_value _ _ shadow_sm = _` (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
     conj_tac
     >- (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]) >>
     qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`] mp_tac fn_has_code_split >> simp[]) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disch_tac >> irule (BETA_RULE staged_copy_read_outcome) >> simp[] >>
  qexists_tac `sm` >> simp[] >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> qexists_tac `tv` >> simp[]
QED

Finalise assign_name_copy_read_frontier_mods
