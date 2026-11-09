(* Memory case of the body induction, pop on a module variable
   (bodyMemPopName's second disjunct; S1's compile_pop_storage_sim, with
   immutables excluded by typing as in compile_pop_immutable_sim). *)
Theory bodyMemPopToplevel
Ancestors
  bodyMemoryPreds bodyExprForceMemory bodyMemPopToplevelSim exprSimPopStorage
  exprSimDefs exprSimHyps exprSimHypsDefs exprSimMemDefs exprLowering exprSimSource
  exprLoweringProps compileEnv loweringStateRelDefs context vyperInterpreter vyperTypeEnv
  vyperTypeInvariants vyperTyping vyperTypeSystem

Theorem pop_toplevel_has_decl[local]:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es ==>
  ?ts d. get_module_code cx src = SOME ts /\
         find_var_decl_by_name id ts = SOME d
Proof
  strip_tac >> spose_not_then assume_tac >>
  `!ts. get_module_code cx src = SOME ts ==>
        find_var_decl_by_name id ts = NONE` by
    (rpt strip_tac >> Cases_on `find_var_decl_by_name id ts` >> metis_tac[]) >>
  fs[expr_sim_pre_def, expr_sim_inv_def, env_consistent_def,
     env_context_consistent_def, Once well_typed_expr_def,
     type_place_target_TopLevelNameTarget] >>
  Cases_on `FLOOKUP env.bare_global_assignable (src,id)` >> gvs[] >>
  qpat_x_assum
    `!src id ty. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
                 FLOOKUP env.bare_globals (src,id) = NONE ==> _`
    (qspecl_then [`src`, `id`, `ArrayT ann (Dynamic n)`] mp_tac) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!ts. get_module_code cx src = SOME ts ==> _`
    (qspec_then `ts` mp_tac) >> simp[]
QED

Theorem compile_pop_toplevel_vv_sim_mem:
  !ctx func cenv cx env ty ann nid es.
    expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget nid)) es ==>
    expr_vv_sim_mem ctx func cenv cx ty (Pop ann (TopLevelNameTarget nid)) es
Proof
  rpt strip_tac >> PairCases_on `nid` >>
  drule pop_toplevel_has_decl >> strip_tac >>
  `well_typed_expr env (Pop ann (TopLevelNameTarget (nid0,nid1))) /\
   env_consistent env cx es` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all pop_storage_target_facts >> strip_tac >> gvs[] >>
  irule compile_pop_storage_normalized_vv_sim_mem >> metis_tac[]
QED

Theorem pop_toplevel_compile_not_stack[local]:
  expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (src,id))) es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  compile_expr cenv ty (Pop ann (TopLevelNameTarget (src,id))) sa =
    (StackValue t op,sb) ==> F
Proof
  strip_tac >> drule pop_toplevel_has_decl >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_sim_pre_def] >>
  `well_typed_expr env (Pop ann (TopLevelNameTarget (src,id))) /\
   env_consistent env cx es` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all pop_storage_target_facts >> strip_tac >> gvs[] >>
  drule_all exprSimTopLevelPropsTheory.toplevel_storage_ce_vars >> strip_tac >>
  drule_all pop_storage_compiler_facts >> strip_tac >>
  drule_all compile_expr_pop_storage >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] mp_tac) >> simp[]
QED

Theorem body_pop_toplevel_mem:
  !cx ann nid. body_expr_mem_ok cx (Pop ann (TopLevelNameTarget nid))
Proof
  rpt gen_tac >> PairCases_on `nid` >>
  (rpt gen_tac >> match_mp_tac body_expr_mem_ok_intro >>
   conj_tac >- (rpt strip_tac >> gvs[])) >> rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (Pop ann (TopLevelNameTarget (nid0,nid1))) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  `expr_vv_sim_mem ctx func cenv cx ty (Pop ann (TopLevelNameTarget (nid0,nid1))) es` by
    metis_tac[compile_pop_toplevel_vv_sim_mem] >>
  simp[] >>
  Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`
  >- (irule body_expr_sim_mem_of_vv_sim_mem >> simp[] >>
      conj_tac >- metis_tac[pop_toplevel_compile_not_stack] >>
      goal_assum drule) >>
  rw[expr_sim_mem_def] >>
  gvs[stmt_state_rel_def, state_rel_def]
QED
