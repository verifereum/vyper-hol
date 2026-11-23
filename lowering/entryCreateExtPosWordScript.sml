(* Scope the positional word read at the selected VV child exit. *)
Theory entryCreateExtPosWord
Ancestors
  entryCreateUnwrapSimple bodyFullExtCallPosList bodyFullExtCallPosWord
  exprWordOperand exprSimSource exprSimUnwrap vyperEvalExprPreservesScopesDom
  exprSimHypsDefs exprSimHyps exprOperandVar fragGasSeqPtr valueCopyBytes
  entryCreateFocusSpec bodyFullExtCallPosAggregate compileEnv context
  vyperStorageFootprint loweringPosts vyperState fragGasOriginPtr
  exprLowering exprLoweringProps exprSafeOperand exprSimMemDefs bodyPtrDefs
  bodyMemoryDefs exprSimWordArgs

Theorem extcall_pos_word_snapshot_site:
  expr_body_pre cenv cx env e es /\ is_word_type (expr_type e) /\
  compile_expr cenv (expr_type e) e sa = (vv,si) /\
  compile_snapshot_vv cenv (exprs_can_mutate cenv (xs ++ kw_es))
    (ext_call_arg_value (lowered_value_type cenv e) vv) si = (sv,sb) /\
  local_ptrs_reserved cenv sa /\ fn_has_code si sb func /\ fn_inst_ids_distinct func /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\
  (!tail. eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL tv,ee with gas_obs := tail)) /\
  ee.gas_obs = [] /\ storage_trace_domain cx st0 ee.storage_trace /\
  ~t.vs_halted /\ create_operand_at si t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,ctx,func) cenv cx e (es,sa,si,s0,vv,G0,tn0)
      H (INL tv) ee G tn t) ==>
  ?op v z G' tn'. sv = StackValue (lowered_value_type cenv e) op /\
    read_result cx tv ee = (INL v,ee) /\
    create_operand_full_scope si sb explicit ctx func t [] (OK z) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G',tn') /\
      extcall_positional_post keep_pure DF lo d ctx func cenv cx env
        kw_es [e] [sv] sa sb es s0 G0 tn0 H (INL [v]) ee G' tn' z)
Proof
  strip_tac >> fs[create_operand_at_def] >>
  `post_value_type cenv e = expr_type e /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (simp[] >> drule expr_body_pre_lowered_fits >> simp[]) >>
  `lowered_value_type cenv e = expr_type e` by
    metis_tac[vyperTypeArgFitsTheory.arg_type_fits_prim_word,
              membership_element_word_boundary] >>
  `vv_type (ext_call_arg_value (lowered_value_type cenv e) vv) =
   lowered_value_type cenv e` by metis_tac[extcall_operand_snapshot_type] >>
  `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> create_operand_vv_post _ _ _ _ _ H _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- fs[storage_trace_domain_def]) >>
  simp[create_operand_vv_post_def] >> strip_tac >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv ee t` by metis_tac[vv_post_def] >>
  `unwrap_simple vv` by
    (Cases_on `vv` >> fs[unwrap_simple_def, vv_holds_def] >>
     metis_tac[is_bytestring_word_type]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee` (fn th => pure_rewrite_tac[listTheory.APPEND_NIL, th]) >>
     disch_then ACCEPT_TAC) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[expr_body_pre_gas_obs] >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  `expr_sim_inv cenv cx env ee` by metis_tac[exprSimSourceTheory.expr_body_pre_eval_result] >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  suspend "unwrap"
QED

Resume extcall_pos_word_snapshot_site[unwrap]:
  `sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id` by
    (drule compile_expr_extends >> simp[]) >>
  `local_ptrs_reserved cenv si` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. vv_operand vv = Var x ==> not_fresh_at si x` by
    metis_tac[cj 1 compiler_compile_var] >>
  Cases_on `unwrap_value cenv vv si` >> rename1 `_ = (op,sc)` >>
  `sv = StackValue (lowered_value_type cenv e) op /\ sc = sb` by
    (drule_all word_snapshot_unwrap_copy >> strip_tac >> gvs[comp_bind_def, comp_return_def]) >>
  qpat_x_assum `sc = sb` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa si s0 ee tv vv t /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn t` by
    fs[create_operand_vv_post_def] >>
  drule_at (Pat `unwrap_value _ _ _ = _`) create_unwrap_simple_site >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  qpat_assum `post_value_type cenv e = expr_type e` (fn th =>
    qpat_assum `lowered_value_type cenv e = expr_type e` (fn lty =>
      disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`) o REWRITE_RULE [th,lty]))) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `storage_trace_domain _ _ _`)) >>
  disch_then (qspecl_then [`explicit`, `d`, `ctx`, `PG`] mp_tac) >>
  disch_then (qspec_then `DF` mp_tac) >>
  (impl_tac >-
    (simp[] >> qpat_x_assum `cenv.ce_is_ctor /\ _ ==> _` mp_tac >> simp[])) >>
  strip_tac >> suspend "row"
QED

Resume extcall_pos_word_snapshot_site[row]:
  qexistsl [`op`, `v`, `z`, `G'`, `tn'`] >> simp[] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` drule >> strip_tac >> simp[] >>
  `~z.vs_halted` by
    metis_tac[gas_origin_ptr_path_projections, gas_path_ptr_ok_not_halted] >>
  `si.cs_next_var <= sb.cs_next_var /\ si.cs_next_id <= sb.cs_next_id` by
    (mp_tac (Q.SPECL [`cenv`, `vv`, `si`] ci_mono_unwrap_value) >> simp[ci_mono_def]) >>
  `safe_operand sb op` by
    (irule unwrap_value_safe_operand >> first_assum (irule_at Any) >>
     `well_typed_expr env e` by fs[expr_body_pre_def] >>
     `!id t. FLOOKUP env.var_types id = SOME t ==>
             well_formed_type env.type_defs t` by metis_tac[expr_body_pre_var_types_well_formed] >>
     drule_all (cj 1 compile_expr_word_result) >> simp[]) >>
  drule expr_post_frame >> strip_tac >>
  qpat_assum `post_value_type cenv e = expr_type e` (fn ty =>
    qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def,ty])) >>
  `return_buf_frame d cenv sb z` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`, `s0`, `sa`] >> simp[]) >>
  simp[extcall_positional_post_def, vv_operand_def, vv_location_def, vv_storage_live_def,
       vv_store_bound_def, safe_operand_def] >>
  reverse conj_tac >- fs[safe_operand_def] >>
  qexistsl [`sa`, `si`, `sb`, `vv`, `Value v`, `exprs_can_mutate cenv (xs ++ kw_es)`] >>
  simp[vv_holds_def, vv_at_def, ptr_vv_ok_def, read_result_def, return_def] >>
  fs[exprs_can_mutate_append]
QED

Finalise extcall_pos_word_snapshot_site
