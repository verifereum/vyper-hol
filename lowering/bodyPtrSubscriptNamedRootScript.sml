(* Retained local roots use the local allocation size, at any typed type. *)
Theory bodyPtrSubscriptNamedRoot
Ancestors
  exprSimHypsDefs bodyPtrDefs exprSimDefs loweringPosts
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperValue
  valueEncoding valueEncodingProps codegenRel contextCodegenRel
  compileEnv loweringStateRelDefs ptrDiscipline finite_map exprSimProps venomState
  vyperAST localPtrsProps varsExt exprLoweringProps exprSimNameValue
  vyperInterpreter vyperState fragGasPathPtr context exprLowering

Theorem named_root_preparation:
  expr_body_pre cenv cx env (Name ann id) es /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
  ?entry p sz a.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ann /\
    lookup_var p s = SOME a /\ type_memory_size entry.type <= sz /\
    ptr_covers G tn p s sz /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory entry.type entry.value (w2n a) mem)
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `?a. lookup_var p s = SOME a /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  qexistsl_tac [`entry`, `p`, `sz`, `a`] >> simp[] >>
  fs[ghost_inv_def] >> metis_tac[]
QED

Theorem named_root_source[local]:
  lookup_scopes id es.scopes = SOME entry ==>
  eval_expr cx (Name ann id) es =
    (INL (PlaceR (MemoryPlace id [])),es)
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       type_check_def, assert_def, check_def, ignore_bind_def]
QED

Theorem named_root_execution:
  expr_body_pre cenv cx env (Name ann id) es /\
  compile_expr cenv ty (Name ann id) sa = (vv,sb) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (Name ann id)) (es,s0,G0,tn0)
    (\res ee G tn t. ?entry p sz a.
      res = INL (PlaceR (MemoryPlace id [])) /\
      ee = (es with gas_obs := []) /\ t = s0 /\ G = G0 /\ tn = tn0 /\
      vv = LocatedValue ann (mk_ptr (Var p) LocMemory) /\
      lookup_scopes id ee.scopes = SOME entry /\
      evaluate_type (get_tenv cx) ann = SOME entry.type /\
      value_has_type entry.type entry.value /\
      FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
      lookup_var p t = SOME a /\ type_memory_size entry.type <= sz /\
      ptr_covers G tn p t sz /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
             val_in_memory entry.type entry.value (w2n a) mem) /\
      vv_post ctx func cenv cx (Name ann id) es sa sb s0 ee
        (PlaceR (MemoryPlace id [])) vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule_all named_root_preparation >> strip_tac >>
  drule compile_name_value_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  `vv_post ctx func cenv cx (Name ann id) es sa sa s0
     (es with gas_obs := []) (PlaceR (MemoryPlace id []))
     (LocatedValue ann (mk_ptr (Var p) LocMemory)) s0` by
    (irule name_value_post >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`,
                `G0`, `tn0`, `OK s0`] >>
  simp[named_root_source, gas_path_ptr_rules] >>
  gvs[ghost_inv_def, ghost_kept_def] >> first_assum ACCEPT_TAC
QED
