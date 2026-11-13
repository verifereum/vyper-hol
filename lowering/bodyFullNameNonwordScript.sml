Theory bodyFullNameNonword
Ancestors
  bodySimFull gasOutcomeFullCompose bodyNameNonwordMemory
  exprSimNameValue exprSimSource exprSimHypsDefs bodyPtrDefs
  gasShadow fragGasOriginPtr exprLoweringProps loweringPosts
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncodingProofs
  exprLowering compileEnv exprSimDefs exprSimNameWord exprSimProps loweringSlice
  vyperInterpreter vyperState venomState finite_map context

Theorem name_nonword_memory_post:
  expr_sim_pre cenv cx env (Name ann id) es /\ ~is_word_type ann /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  stmt_state_rel H ctx func cenv cx es s /\
  storage_well_formed_on cx es (FST H) ==>
  expr_post H ctx func cenv cx (Name ann id) es sa sa s
    (es with gas_obs := []) entry.value (Var p) s
Proof
  strip_tac >> drule_all bodyNameMemoryFactsTheory.body_name_source_region >>
  strip_tac >> gvs[] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `vv_post H ctx func cenv cx (Name ann id) es sa sa s
    (es with gas_obs := []) (PlaceR (MemoryPlace id []))
    (LocatedValue ann (mk_ptr (Var p) LocMemory)) s` by
    (irule name_value_post >> simp[]) >>
  `read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
    (INL entry.value, es with gas_obs := [])` by
    (qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := []`, `entry`]
      mp_tac eval_name_word >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def]) >>
  drule_all exprSimUnwrapPropsTheory.vv_post_read_result >> strip_tac >>
  drule exprSimUnwrapPropsTheory.expr_post_of_vv_post_memory >>
  simp[mk_ptr_def]
QED

Theorem name_nonword_ghost_posts:
  expr_body_pre cenv cx env (Name ann id) es /\ ~is_word_type ann /\
  lookup_scopes id es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s ==>
  ptr_val_ok cx (post_value_type cenv (Name ann id)) entry.value (Var p) G tn s /\
  ptr_buf_ok cenv (Name ann id) (Var p) G s
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env (Name ann id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule_all bodyNameMemoryFactsTheory.body_name_source_region >> strip_tac >> gvs[] >>
  `ptr_covers G tn p s sz /\
   !w mem. lookup_var p s = SOME w /\
      mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  `type_memory_bytes cenv ann = type_memory_size entry.type` by
    (drule exprSimHypsTheory.expr_body_pre_copy_ok >>
     disch_then (qspec_then `entry.type` mp_tac) >>
     simp[vyperASTTheory.expr_type_def]) >>
  simp[ptr_val_ok_def, post_value_type_def, lowered_value_type_def,
       vyperASTTheory.expr_type_def, ptr_buf_ok_def, ptr_mem_ok_def,
       eval_operand_def] >>
  gvs[ptr_covers_def] >> drule val_store_size_le >> strip_tac >> decide_tac
QED

Theorem name_nonword_full:
  expr_body_pre cenv cx env (Name ann id) es /\ ~is_word_type ann ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es
Proof
  rw[expr_sim_full_def] >>
  `expr_sim_pre cenv cx env (Name ann id) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  `?entry. lookup_scopes id es.scopes = SOME entry` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> metis_tac[]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >>
  gvs[lower_value_def, comp_bind_def, comp_return_def,
      unwrap_value_def, contextTheory.mk_ptr_def] >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G0`, `es`, `INL entry.value`, `s0`, `tn0`] >>
  conj_tac
  >- (gen_tac >>
      qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
        mp_tac eval_name_word >> simp[vyperStateTheory.bind_def]) >>
  simp[] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all name_nonword_ghost_posts >> strip_tac >>
  simp[gas_origin_ptr_path_rules, ghost_kept_at_def] >>
  all_tac >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
  >- (irule name_nonword_memory_post >> simp[] >> qexists_tac `env` >> simp[]) >>
  all_tac >~ [`expr_store_bound _ _ _ _ _`]
  >- (drule_all bodyNameMemoryFactsTheory.body_name_source_region >>
      strip_tac >> gvs[exprSimMemDefsTheory.expr_store_bound_def, vyperASTTheory.expr_type_def,
                      eval_operand_def] >>
      rpt strip_tac >> gvs[] >> drule val_store_size_le >> strip_tac >> decide_tac) >>
  gvs[ghost_inv_at_def] >> metis_tac[]
QED
