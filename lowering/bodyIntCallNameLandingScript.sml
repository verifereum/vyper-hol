(* Local Name is a semantic producer before protected value forcing. *)
Theory bodyIntCallNameLanding
Ancestors
  exprSimNameValue bodyIntCallForceLanding exprSimHypsDefs exprSimDefs
  loweringPosts exprLowering exprLoweringProps compileEnv context
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperAST vyperState
  vyperInterpreter finite_map

Theorem protected_name_value_binding:
  expr_sim_pre ce cx env (Name ann id) es /\
  stmt_state_rel ctx func ce cx es s ==>
  ?p sz v.
    compile_expr ce ann (Name ann id) sa =
      (LocatedValue ann (mk_ptr (Var p) LocMemory),sa) /\
    vv_holds ce cx ann (PlaceR (MemoryPlace id []))
      (LocatedValue ann (mk_ptr (Var p) LocMemory))
      (es with gas_obs := []) s /\
    read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
      (INL v,es with gas_obs := []) /\
    FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `ce.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  drule_all name_value_post >> strip_tac >>
  `vv_holds ce cx ann (PlaceR (MemoryPlace id []))
    (LocatedValue ann (mk_ptr (Var p) LocMemory))
    (es with gas_obs := []) s` by
    fs[vv_post_def, expr_type_def] >>
  `?v. read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
    (INL v,es with gas_obs := [])` by
    (fs[vv_holds_def, mk_ptr_def] >> metis_tac[]) >>
  qexistsl_tac [`p`, `sz`, `v`] >> simp[] >>
  irule compile_name_value_ptr >> simp[]
QED

Theorem protected_name_value_landing:
  expr_sim_pre ce cx env (Name ann id) es /\
  lower_value compile_expr ce ann (Name ann id) sa = (op,sb) /\
  stmt_state_rel ctx func ce cx es s /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ local_ptrs_reserved ce sa /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) ==>
  ?v u. read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
      (INL v,es with gas_obs := []) /\
    gas_path ctx func s 0 (OK u) /\ expr_val_rel cx ann v op u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name base sz. local_region ce scopes u name base sz <=>
      local_region ce scopes s name base sz)
Proof
  strip_tac >> drule_all protected_name_value_binding >>
  disch_then (qspec_then `sa` strip_assume_tac) >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> strip_tac >>
  gvs[mk_ptr_def] >>
  drule protected_memory_value_forcing >> simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`scopes`, `ctx`] mp_tac) >> simp[]
QED
