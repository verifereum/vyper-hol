(* Typed local regions used by memory-safe Name compilation. *)
Theory bodyNameMemoryFacts
Ancestors
  exprSimSource exprSimHypsDefs exprSimDefs exprSimProps exprSimMemDefs bodyMemoryDefs
  exprSimMemoryValues exprSimMemoryStack fragGasSeqMem fragGasPathMem
  gasNormalPrefix gasSummary gasContext gasCount fragGasMode loweringPosts
  exprSimNameWord exprSimNameValue memoryValueEncoding loweringSlice exprLowering exprLoweringProps
  fragExec fragExecMem allocaHistoryFragment instMemFrontier
  emitHelperProps emitHelper compileEnv loweringStateRelDefs context venomInst venomState
  venomExecSemantics venomMemDefs vyperInterpreter vyperState vyperAST
  vyperTypeEnv vyperTypeSystem vyperTypeInvariants valueEncoding valueEncodingProofs
  list rich_list finite_map words arithmetic

Theorem body_word_name_region:
  expr_sim_pre ce cx env (Name ann id) es /\ word_value_type ann /\
  stmt_state_rel ctx func ce cx es s ==>
  ?entry p sz w.
    lookup_scopes id es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    word_value entry.value /\ lookup_var p s = SOME w /\
    local_region ce es.scopes s id (w2n w) sz /\ 32 <= sz
Proof
  rpt strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `?w. lookup_var p s = SOME w /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  drule_all word_value_type_memory_size >> strip_tac >>
  drule_all word_value_type_typed >> strip_tac >>
  qexistsl_tac [`entry`, `p`, `sz`, `w`] >>
  simp[local_region_def] >> metis_tac[]
QED

Theorem body_word_name_MLOAD_frontier:
  expr_sim_pre ce cx env (Name ann id) es /\ word_value_type ann /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  inst_mem_below_frontier (mk_inst iid MLOAD [Var p] outs) s
Proof
  rpt strip_tac >> drule_all body_word_name_region >> strip_tac >>
  gvs[] >> irule body_local_ptr_MLOAD_frontier >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[n2w_w2n]
QED

Theorem body_name_source_region:
  expr_sim_pre ce cx env (Name ann id) es /\
  stmt_state_rel ctx func ce cx es s ==>
  ?entry p sz w.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\
    local_region ce es.scopes s id (w2n w) sz /\
    type_memory_size entry.type <= sz /\ val_wf entry.type entry.value /\
    val_in_memory entry.type entry.value (w2n w) s.vs_memory /\
    w2n w + sz <= s.vs_alloca_next
Proof
  rpt strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `?w. lookup_var p s = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value /\
       val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> strip_tac >> qexists_tac `w` >>
     simp[] >> irule memory_value_rel_val_in_memory >> simp[]) >>
  `local_region ce es.scopes s id (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  drule_all body_local_region_frontier >> strip_tac >>
  qexistsl [`entry`, `p`, `sz`, `w`] >> simp[]
QED


(* A local's pointer, its type-sized region and its rounded value footprint
   lie below the frontier. *)
Theorem name_vv_store_bound:
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  val_wf entry.type entry.value /\ lookup_var p s = SOME w /\
  type_memory_size entry.type <= sz /\ w2n w + sz <= s.vs_alloca_next ==>
  vv_store_bound cx ann ann (es with gas_obs := []) (PlaceR (MemoryPlace id []))
    (LocatedValue ann (mk_ptr (Var p) LocMemory)) s
Proof
  simp[vv_store_bound_def, contextTheory.mk_ptr_def, eval_operand_def] >>
  rpt strip_tac >~ [`val_store_size`]
  >- (`read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
         (INL entry.value, es with gas_obs := [])` by
        (qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := []`, `entry`]
           mp_tac eval_name_word >>
         simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
              type_check_def, assert_def, check_def, ignore_bind_def]) >>
      gvs[] >> drule val_store_size_le >> decide_tac) >>
  gvs[]
QED
