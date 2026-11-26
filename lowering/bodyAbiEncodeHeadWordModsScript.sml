(* A word argument is forced at its own snapshot, without an aggregate copy. *)
Theory bodyAbiEncodeHeadWordMods
Ancestors
  bodyAbiEncodePackedPostMods bodyECRecoverOperandHeadMods bodyForcedStorageFrameMods
  bodyWriteSubscriptSourceMods exprBodyPreProps exprBodyPreTypingProps
  exprReasonOperand exprOperandVar exprSimWordArgs exprSimUnwrap exprLoweringProps
  gasShadowCompile gasShadowCompileHelpers gasShadowCompileConvert
  aggregateEvaluatedLayout abiEncodeArgsSim vyperTypeArgFits vyperEventArgCompat
  bodyMemoryDefs vyperStorageTrace bodyFullPredsMods bodyFullPostsMods
  compileEnv exprLowering vyperAST vyperTypeSystem exprSimHypsDefs loweringPosts
  vyperState gasOutcomeFullPostMods bodyPtrDefs exprSimMemDefs venomState
  gasShadowCompilePure gasShadowState vyperInterpreter context gasShadow
Libs monadsyntax

Theorem abi_word_snapshot_type[local]:
  !cenv e. expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
    is_word_type (lowered_value_type cenv e) ==>
    lowered_value_type cenv e = expr_type e
Proof
  ho_match_mp_tac lowered_value_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`IntCall`]
  >- (strip_tac >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      fs[Once well_typed_expr_def] >> drule_all expr_sim_inv_mods_return_type >>
      strip_tac >> gvs[lowered_value_type_def,expr_type_def,type_widens_to_def,
                      event_arg_compatible_alias_def] >>
      metis_tac[arg_type_fits_word_type,abi_args_word_fits_eq])
  >~ [`Concat`]
  >- (Cases_on `ty` >> simp[lowered_value_type_def,concat_buffer_type_def,is_word_type_def] >>
      rename1 `BaseT b` >> Cases_on `b` >> simp[is_word_type_def]) >>
  simp[lowered_value_type_def,is_word_type_def,expr_type_def]
QED

Theorem abi_word_snapshot_value[local]:
  is_word_type (expr_type e) /\ vv_type vv = expr_type e /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  compile_snapshot_vv ce copy (ext_call_arg_value (expr_type e) vv) sm = (sv,ss) ==>
  ?op. lower_value compile_expr ce (expr_type e) e si = (op,ss) /\
       sv = StackValue (expr_type e) op
Proof
  strip_tac >>
  `ext_call_arg_value (expr_type e) vv = vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def,vv_type_def]) >>
  Cases_on `unwrap_value ce vv sm` >>
  gvs[lower_value_def,compile_snapshot_vv_def,comp_bind_def,comp_return_def]
QED

Theorem abi_word_snapshot_pair[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  is_word_type (lowered_value_type cenv e) /\
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
    shadow_si = (vv,shadow_sm) /\
  compile_snapshot_vv cenv copy
    (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  compile_snapshot_vv (gas_shadow_env T cenv) copy
    (ext_call_arg_value (lowered_value_type cenv e) vv) shadow_sm = (sv,shadow_ss) ==>
  lowered_value_type cenv e = expr_type e /\ is_word_type (expr_type e) /\
  ?op. sv = StackValue (expr_type e) op /\
       lower_value compile_expr cenv (expr_type e) e si = (op,ss) /\
       lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
         (gas_shadow_expr e) shadow_si = (op,shadow_ss)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac abi_word_snapshot_type >>
  `is_word_type (expr_type e)` by fs[] >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     fs[expr_sim_inv_mods_def]) >>
  `vv_type vv = expr_type e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `vv` >> gvs[reason_result_shape_def,vv_type_def]) >>
  fs[gas_shadow_expr_type] >>
  drule_at_then (Pat `compile_expr _ _ _ si = _`) drule abi_word_snapshot_value >>
  strip_tac >>
  drule_at_then (Pat `compile_expr _ _ (gas_shadow_expr _) _ = _`) drule
    (SIMP_RULE bool_ss [gas_shadow_expr_type]
      (Q.INST [`e` |-> `gas_shadow_expr e`] abi_word_snapshot_value)) >>
  strip_tac >>
  qpat_x_assum `!sv ss copy. _ /\ compile_snapshot_vv _ _ _ shadow_sm = _ ==> _`
    (qspecl_then [`sv`,`shadow_ss`,`copy`] mp_tac) >>
  qpat_x_assum `!sv ss copy. _ /\ compile_snapshot_vv _ _ _ sm = _ ==> _`
    (qspecl_then [`sv`,`ss`,`copy`] mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[]
QED

val word_post = ``\(H:(bool # 256 word # type_value) list # num list) res ee G tn t.
  abi_encode_packed_post_mods mods DF lo d ctx func cenv cx env
    [e] [sv] si ss es s0 G0 tn0 H res ee G tn t``;

Theorem abi_encode_head_word_mods:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  is_word_type (lowered_value_type cenv e) /\
  compile_expr cenv (expr_type e) e si = (vv,sm) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
    shadow_si = (vv,shadow_sm) /\
  compile_snapshot_vv cenv copy
    (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
  compile_snapshot_vv (gas_shadow_env T cenv) copy
    (ext_call_arg_value (lowered_value_type cenv e) vv) shadow_sm = (sv,shadow_ss) /\
  expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (si,ss,shadow_si,shadow_ss) /\
  local_ptrs_reserved cenv si /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv si s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = si.cs_current_bb /\
  s0.vs_inst_idx = LENGTH si.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\ (^word_post) H (INL [v]) ee G tn t /\
      ee.gas_obs = [] /\ (?obs. ee.storage_trace = es.storage_trace ++ obs) /\
      (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  strip_tac >> drule_all_then strip_assume_tac abi_word_snapshot_pair >>
  drule_all_then assume_tac ecrecover_operand_head_run_mods >>
  irule gas_outcome_full_mods_post_source >>
  first_assum (irule_at Any) >> simp[] >> rpt gen_tac >> strip_tac >>
  suspend "normal"
QED

Resume abi_encode_head_word_mods[normal]:
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx) (es with gas_obs := xs) = (INL v,ee)` by
    (qpat_x_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := xs) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := xs)` by simp[] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  drule_then strip_assume_tac (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` kall_tac >>
  drule_then (assume_tac o SIMP_RULE bool_ss []) compile_lower_value_var >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` kall_tac >>
  drule_then strip_assume_tac compile_expr_extends >>
  `ci_mono sm ss` by
    (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`sm`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `si.cs_next_var <= ss.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  fs[expr_post_mods_def] >> drule_then assume_tac expr_post_frame >>
  `post_value_type cenv e = expr_type e` by simp[post_value_type_word] >>
  fs[expr_post_def] >>
  qpat_x_assum `ci_mono _ _` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `return_buf_frame d cenv ss t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`si`] >> simp[]) >>
  simp[abi_encode_packed_post_mods_def,vv_operand_def] >>
  conj_tac
  >- (map_every qexists_tac [`si`,`sm`,`ss`,`vv`,`copy`] >>
      simp[abi_encode_saved_row_mods_def,ci_mono_def,vv_location_def] >>
      qexists_tac `Value v` >>
      simp[vv_holds_mods_def,vv_holds_def,vv_at_def,expr_val_at_def,
           ptr_vv_ok_def,vv_store_bound_def,read_result_def,return_def]) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  drule_all storage_trace_frame_prefix >> simp[]
QED

Finalise abi_encode_head_word_mods
