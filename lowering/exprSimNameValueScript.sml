(* Counted raw value simulation for local names. *)
Theory exprSimNameValue
Ancestors
  exprSimHypsDefs exprSimProps exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasPath fragGasMode
  list finite_map fragExec localPtrsProps loweringSlice
  exprLowering exprLoweringProps compileEnv context
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeEnv vyperTypeInvariants
  valueEncoding valueEncodingProofs venomInst venomState

Theorem name_value_marked_exec:
  lookup_scopes id es.scopes = SOME entry /\ ~s0.vs_halted ==>
  gas_marked_exec F (ctx,func) (eval_expr cx (Name ann id)) (es,s0)
    [] (INL (PlaceR (MemoryPlace id []))) es (OK s0)
Proof
  strip_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
       Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def]
QED

Theorem compile_name_value_ptr:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  compile_expr cenv ty (Name ann id) sa =
    (LocatedValue ann (mk_ptr (Var p) LocMemory),sa)
Proof
  simp[compile_expr_def, compile_name_vv_def, comp_return_def,
       vyperASTTheory.expr_type_def]
QED

Theorem name_value_post:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  value_has_type entry.type entry.value /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
  cenv.ce_var_type id = SOME ann /\
  stmt_state_rel ctx func cenv cx es s0 ==>
  vv_post ctx func cenv cx (Name ann id) es sa sa s0
    (es with gas_obs := []) (PlaceR (MemoryPlace id []))
    (LocatedValue ann (mk_ptr (Var p) LocMemory)) s0
Proof
  strip_tac >>
  `read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
     (INL entry.value, es with gas_obs := [])` by
    (qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := []`, `entry`]
       mp_tac eval_name_word >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          type_check_def, assert_def, check_def, ignore_bind_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[]) >>
  `?w. lookup_var p s0 = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value /\
       val_in_memory entry.type entry.value (w2n w) s0.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  simp[vv_post_def, vv_holds_def, vv_at_def, mk_ptr_def,
       vyperASTTheory.expr_type_def, eval_operand_def, locals_kept_mem] >>
  conj_tac >- metis_tac[val_in_memory_word_type] >>
  disj2_tac >> disj1_tac >>
  qexistsl_tac [`id`, `w2n w`, `sz`] >>
  asm_simp_tac (srw_ss()) [local_region_def] >>
  drule val_footprint_le >> strip_tac >>
  conj_tac >- decide_tac >>
  conj_tac >- (irule local_path_at_val_at >> irule local_path_at_root >> simp[]) >>
  irule local_place_at_root >> simp[]
QED

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
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `OK s0`] >>
  conj_tac >- (irule name_value_marked_exec >> simp[]) >>
  disj1_tac >> simp[] >> irule name_value_post >> simp[]
QED

