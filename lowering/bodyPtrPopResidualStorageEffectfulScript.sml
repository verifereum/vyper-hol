(*
 * Held residual of pop_expr_ptr_ok (bodyPtrPop): pop on a nested target
 * rooted at a storage or transient variable with an index that is not
 * pure (it pops or calls), which can leave the target's header dead when
 * the pop reads it.  The pointer twin of S1's
 * exprSimPopNestedStorageEffectful.pop_nested_storage_effectful_sim,
 * whose own dead-header case is still admitted in S1.
 *
 * TOP-LEVEL:
 *   pop_nested_storage_effectful_dead_case_ptr
 *)
Theory bodyPtrPopResidualStorageEffectful
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs targetPlaceSim
  targetPlaceLive vyperPureExpr vyperInterpreter vyperState vyperAST

(* RESIDUAL: held per argon ruling 2026-11-08; closed with S1's twin (exprSimPopNestedStorageEffectful.pop_nested_storage_effectful_dead_case) once the shared dead-slot storage frame lands *)
Theorem pop_nested_storage_effectful_dead_case_ptr:
  !tops ctx cenv cx env ann bt ty es d PG func src id ts vd.
    body_inv tops ctx cenv cx /\
    body_base_target_ptr_ok cx bt /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME vd /\
    ~EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
