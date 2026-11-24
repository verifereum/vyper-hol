(* Direct joint local-place simulation for Name. *)
Theory bodyFullNameVV
Ancestors
  bodySimFull gasOutcomeFullCompose exprSimHyps abiBuiltinEncodeWord
  bodyFullEmptyLeafData exprSimFullBundleProps
  bodyPtrDefs fragGasOriginPtr exprSimNameValue exprSimNameWord exprSimSource
  exprLoweringProps entryDecodeStaticProps vyperTyping loweringSlice exprSimProps
  exprSimHypsDefs exprSimDefs vyperTypeEnv vyperInterpreter vyperState
  bodyNameMemoryFacts exprLowering context compileEnv loweringStateRelDefs
  venomState finite_map vyperAST valueEncoding vyperTypeSystem vyperTypeCallGraph

Theorem name_vv_nil:
  expr_body_pre cenv cx env (Name ann id) es /\
  expr_vv_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es (st0,sa,sb,sha,shb,vv,s0,G0,tn0) ==>
  sb = sa /\
  (!tail. eval_expr cx (Name ann id) (es with gas_obs := tail) =
          (INL (PlaceR (MemoryPlace id [])), es with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx (Name ann id)
         (es,sa,sb,s0,vv,G0,tn0) H (INL (PlaceR (MemoryPlace id [])) : eval_result + exception)
         (es with gas_obs := []) G0 tn0 s0)
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env (Name ann id) es` by
    gvs[expr_sim_pre_body, int_calls_expr_def] >>
  `?entry. lookup_scopes id es.scopes = SOME entry` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> metis_tac[]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  fs[expr_vv_sim_full_hypotheses_def, expr_sim_full_code_def] >>
  drule compile_name_value_ptr >> strip_tac >> gvs[] >>
  conj_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def] >>
  simp[expr_vv_sim_full_post_def, expr_sim_full_endpoint_def] >>
  gen_tac >> disch_tac >> first_x_assum drule >> strip_tac >>
  drule_all body_name_source_region >> strip_tac >> gvs[] >>
  conj_tac >- (irule name_value_post >> simp[] >> metis_tac[]) >>
  conj_tac >- (simp[expr_type_def, lowered_value_type_def] >>
               irule name_vv_store_bound >> simp[] >> metis_tac[]) >>
  simp[ghost_kept_at_def, mk_ptr_def, vv_location_def, expr_type_def] >>
  conj_tac >- (gvs[ghost_inv_at_def] >> metis_tac[]) >>
  gvs[ghost_inv_at_def] >>
  `ptr_covers G0 tn0 p s0 sz /\
   !mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem` by metis_tac[] >>
  `read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
     (INL entry.value, es with gas_obs := [])` by
    (`lookup_scopes id (es with gas_obs := []).scopes = SOME entry` by simp[] >>
     pop_assum (mp_then Any mp_tac eval_name_word) >>
     disch_then (qspecl_then [`cx`, `ann`] mp_tac) >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def]) >>
  conj_tac
  >- (simp[ptr_vv_ok_def, ptr_mem_ok_def, eval_operand_def] >>
      drule val_store_size_le >> gvs[ptr_covers_def] >> metis_tac[]) >>
  `type_memory_bytes cenv ann = type_memory_size entry.type` by
    (Cases_on `is_word_type ann`
     >- metis_tac[abi_builtin_encode_word_info, word_type_memory_size] >>
     drule expr_body_pre_copy_ok >>
     disch_then (qspec_then `entry.type` mp_tac) >> simp[expr_type_def]) >>
  gvs[ptr_buf_ok_def, lowered_value_type_def, expr_type_def,
      eval_operand_def, ptr_covers_def] >> metis_tac[]
QED

Theorem name_vv_full:
  expr_body_pre cenv cx env (Name ann id) es ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es
Proof
  rw[expr_vv_sim_full_via_bundle] >>
  drule_all name_vv_nil >> strip_tac >>
  irule (Q.ISPEC `INL (PlaceR (MemoryPlace id [])) : eval_result + exception`
    gas_outcome_full_unchanged) >> gvs[expr_vv_sim_full_hypotheses_def]
QED
