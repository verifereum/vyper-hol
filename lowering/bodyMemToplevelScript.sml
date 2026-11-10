(* Memory case of the body induction (bodyMemory's body_mem_mutual): a module
   variable or immutable.  The value judgment is bodyToplevelMemory's; the
   forced one is the generic unwrap, since an admissible top-level name
   compiles to a storage, transient or code pointer, never a stack value. *)
Theory bodyMemToplevel
Ancestors
  bodyMemoryPreds bodyExprForceMemory bodyToplevelMemory exprSimTopLevelProps
  exprSimHyps exprSimSource exprSimMemDefs exprSimDefs exprLowering
  exprSimHypsDefs vyperTypeCallGraph exprLoweringProps compileEnv loweringStateRelDefs context vyperAST
  vyperInterpreter vyperTypeGlobalLookupSoundness

Theorem toplevel_compile_not_stack[local]:
  expr_body_pre cenv cx env (TopLevelName ann (src,id)) es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  compile_expr cenv ty (TopLevelName ann (src,id)) sa = (StackValue t op,sb) ==>
  F
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  drule expr_body_pre_vv_gas_admissible >> strip_tac >>
  Cases_on `get_module_code cx src`
  >- metis_tac[missing_module_not_gas_admissible] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (`env_consistent env cx es /\ state_well_typed es /\
       well_typed_expr env (TopLevelName ann (src,id))` by
        fs[expr_sim_pre_def, expr_sim_inv_def] >>
      drule_all toplevel_find_NONE_bare_global >> strip_tac >>
      `src = cenv.ce_module /\
       ?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
         !tv. evaluate_type (get_tenv cx) ann = SOME tv ==>
              off + type_memory_size tv < dimword (:256)` by
        (fs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
      qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
      simp[compile_expr_def]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]) >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  rename1 `StorageVarDecl tr _` >> Cases_on `tr` >> simp[compile_expr_def]
QED

Theorem body_toplevel_mem_ok:
  !cx ann src id. body_expr_mem_ok cx (TopLevelName ann (src,id))
Proof
  rpt gen_tac >> pure_rewrite_tac[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es` by
    simp[expr_sim_pre_body, int_calls_expr_def] >>
  `expr_vv_sim_mem ctx func cenv cx ty (TopLevelName ann (src,id)) es` by
    metis_tac[compile_toplevel_name_vv_sim_mem] >>
  simp[] >>
  Cases_on `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx`
  >- (irule body_expr_sim_mem_of_vv_sim_mem >> simp[] >>
      conj_tac >- metis_tac[toplevel_compile_not_stack] >>
      goal_assum drule) >>
  rw[expr_sim_mem_def] >> gvs[stmt_state_rel_def, state_rel_def]
QED
