(* A word snapshot is the scalar expression's lower_value interval. *)
Theory bodyExtPosWordHeadMods
Ancestors
  bodyCopyReadPhysicalTypeMods aggregateEvaluatedLayout abiEncodeArgsSim
  exprReasonOperand gasShadowCompileBase exprLowering loweringPosts compileEnv context
  exprBodyPreProps exprBodyPreTypingProps exprSimHypsDefs
  bodyFullPredsMods bodyFullPostsMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  bodyFullIfExpReach exprLoweringProps exprOperandVar freshWrites exprSimWordArgs
  bodyMemoryDefs exprSimMemDefs bodyPtrDefs vyperAST vyperState

Theorem ext_pos_word_code[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  is_word_type (lowered_value_type cenv e) /\
  compile_expr cenv (expr_type e) e sa = (vv,si) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
    shadow_sa = (vv,shadow_si) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)
    si = (sv,sm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)
    shadow_si = (sv,shadow_sm) ==>
  lowered_value_type cenv e = expr_type e /\
  ?op. sv = StackValue (expr_type e) op /\
       lower_value compile_expr cenv (expr_type e) e sa = (op,sm) /\
       lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_sa = (op,shadow_sm)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac copy_lowered_fits_mods >>
  `is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
  drule_all_then assume_tac abi_args_word_fits_eq >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     fs[expr_sim_inv_mods_def]) >>
  `vv_type vv = expr_type e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `vv` >> gvs[reason_result_shape_def,vv_type_def]) >>
  `ext_call_arg_value (expr_type e) vv = vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def,vv_type_def]) >>
  Cases_on `unwrap_value cenv vv si` >>
  Cases_on `unwrap_value cenv vv shadow_si` >>
  gvs[lower_value_def,compile_snapshot_vv_def,comp_bind_def,comp_return_def]
QED

Theorem ext_pos_word_head_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  body_expr_full_ok_mods mods exps cx e /\ is_word_type (lowered_value_type cenv e) /\
  compile_expr cenv (expr_type e) e sa = (vv,si) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
    shadow_sa = (vv,shadow_si) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)
    si = (sv,sm) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)
    shadow_si = (sv,shadow_sm) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sm shadow_sm /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sm func /\
  fn_has_code shadow_sa shadow_sm shadow_func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ci_mono sa sm /\ ci_mono shadow_sa shadow_sm /\
  (!x. vv_operand sv = Var x ==> not_fresh_at sm x) /\
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v op. res = INL v /\ sv = StackValue (lowered_value_type cenv e) op /\
      (?raw. read_result cx raw ee = (INL v,ee) /\
        vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv ee t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sm ee raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
      vv_storage_live H cx sv ee t /\ stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sm t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\ alloca_history func t /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts /\ wb_frame cenv es ee sa s0 t /\
      (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all_then strip_assume_tac ext_pos_word_code >>
  conj_asm1_tac
  >- (qspec_then `sa` mp_tac
        (Q.SPECL [`cenv`,`expr_type e`,`e`] ci_mono_lower_value_compile_expr) >> simp[]) >>
  conj_tac
  >- (qspec_then `shadow_sa` mp_tac
        (Q.SPECL [`gas_shadow_env T cenv`,`expr_type e`,`gas_shadow_expr e`]
         ci_mono_lower_value_compile_expr) >> simp[]) >>
  conj_tac
  >- (simp[vv_operand_def] >> rpt strip_tac >>
      metis_tac[compile_lower_value_var]) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_mods_def] >> strip_tac >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                   _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,
                    `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
  qhdtm_x_assum `expr_sim_full_mods` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi_mods] >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ ExprQ ExprR` >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
     (\H res ee G tn t. ExprQ H res ee G tn t /\
       (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)) ExprR` by
    (irule gas_outcome_full_mods_post_path >>
     qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ ExprQ ExprR` (irule_at Any) >>
     rpt gen_tac >> strip_tac >> simp[] >>
     metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ (\H res ee G tn t. _ /\ _) ExprR` (irule_at Any) >>
  simp[Abbr `ExprQ`,Abbr `ExprR`] >> rpt gen_tac >> strip_tac >>
  suspend "saved_word"
QED

Resume ext_pos_word_head_mods[saved_word]:
  `is_word_type (expr_type e)` by metis_tac[] >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_lowered] >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  qpat_assum `post_value_type _ _ = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qexists_tac `v` >> simp[] >>
  conj_tac
  >- (qexists_tac `Value v` >>
      simp[vv_holds_mods_def,vv_holds_def,vv_at_def,ptr_vv_ok_def,vv_store_bound_def,
           read_result_def,return_def] >> fs[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
  simp[] >> fs[ci_mono_def]
QED

Finalise ext_pos_word_head_mods
