(* Counted raw value simulation for local names. *)
Theory exprSimNameValue
Ancestors
  exprSimHypsDefs exprSimProps exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasPath fragGasMode
  list finite_map fragExec localPtrsProps loweringSlice
  exprLowering exprLoweringProps compileEnv context
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeEnv vyperTypeInvariants
  valueEncoding valueEncodingProofs venomInst venomState

Theorem compile_name_vv_sim:
  !cenv ann id. expr_vv_ok cenv (Name ann id)
Proof
  rw[expr_vv_ok_def, expr_vv_sim_def] >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all vyperTypeEnvTheory.well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule_then (qspecl_then [`cx`, `ann`] assume_tac) eval_name_word >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def,
       read_result_def] >> strip_tac >>
  gvs[compile_expr_def, compile_name_vv_def, comp_return_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule frag_exec_refl >> rpt strip_tac >> gvs[] >>
  `?w. lookup_var p s = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value /\
       val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, read_result_def, return_def,
       vyperASTTheory.expr_type_def, eval_operand_def] >>
  rpt conj_tac
  >- metis_tac[val_in_memory_word_type]
  >- (disj2_tac >> disj1_tac >>
      qexistsl_tac [`id`, `w2n w`, `sz`] >>
      asm_simp_tac (srw_ss()) [local_region_def, dynarray_local_def] >>
      drule val_footprint_le >> decide_tac) >>
  rpt strip_tac >> gvs[]
QED
