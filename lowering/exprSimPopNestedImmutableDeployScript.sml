(*
 * Pop on a nested target: pop_nested_immutable_deploy_sim, a case of exprSimPopNested on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimPopNestedImmutableDeploy
Ancestors
  exprSimPopNestedBase exprSimPopImmutableTarget
  loweringPosts bodySim
  list fragExec exprSimDefs exprSimProps exprSimHyps exprSimPop exprSimPopStorage
  targetPlaceSim targetPlaceSimCases vyperTypeEnv vyperTypeInvariants
  exprLowering vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeSystem vyperTypeCallGraph vyperCompiler stmtLowering
  venomExecSemantics venomInst venomState emitHelper emitHelperProps
  exprLoweringProps compileEnv finite_map vyperPureExpr
  vyperStoragePlaceRegion vyperStoragePlaceProvenance
  vyperPlaceFrames vyperStatePreservation

(* Pop on a member of an immutable in the constructor, which Python's
   checker accepts for a complex immutable (local.py skips the
   modification count when var_info is None), with pure indices.  The
   lowering (nested_pop_compile_eq, compile_dynarray_pop) walks the target
   to a code-location pointer, loads the length through the immutables
   buffer (compile_ptr_load: in the constructor an MLOAD at immutable
   base 0 plus the offset), asserts it nonzero, stores the decremented
   length (compile_ptr_store, an ISTORE) and returns the pointer to the
   last element.  The target's indices are lowered by compile_expr, so
   their judgments (target_idx_case) are a premise, as target_case_all
   takes them; the ce_is_ctor and ce_module_var_type premises also follow
   from expr_sim_inv's bare_globals_layout (pop_nested_immutable_root_ctor).

   Why it holds (admitted pending alan):
   - the result: vv_holds of a LocatedValue at LocCode is immutable_holds,
     whose constructor disjunct reads the element from memory at
     off + k + 32 + (len-1) * elem_size, past the stored length word
     (pop_path_elem_in_memory is the memory version); vv_at at LocCode is
     vacuous; the source value is LAST vs (pop_place, popped_value);
   - immutables_rel: the popped immutable's new value is in memory by the
     path lemma (val_in_memory_pop_path, stated with Replace (FRONT vs)),
     and immutable_value_bytes_rel's T positions after the pop are the new
     length word plus a subset of the old ones; every other immutable is
     in bare_globals (bare_globals_layout's first clause) and its region
     disjoint (its third), so immutables_rel_mem_agree carries it over;
   - frames: immutable_decl_sep separates the declared immutable's region
     from every vs_allocas entry and every live local, and the store lies
     inside that region (k + 32 <= type_memory_size);
   - errors: an empty array is RuntimeError "pop empty" in the source and
     a failing ASSERT in Venom, which expr_exit accepts;
   - gas: as pop_nested_storage_pure_sim (gas_outcome split,
     gas_exempt_cert_error_place on the error branch).
   imm_target_walk is stated over eval_base_place; Pop evaluates with
   eval_target_place. *)
Theorem pop_nested_immutable_deploy_pure_sim:
  !ctx func cenv cx env ann bt ty es src id nocalls.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    target_idx_case nocalls ctx func cenv cx bt /\
    (nocalls ==> int_calls_target bt = []) /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    EVERY pure_expr (target_indices bt) /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(* By the indices: pure ones by pop_nested_immutable_deploy_pure_sim; one
   that pops or calls is exprSimPopImmutableTarget's residual
   pop_nested_immutable_deploy_impure_index_case. *)
Theorem pop_nested_immutable_deploy_sim:
  !ctx func cenv cx env ann bt ty es src id nocalls.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    target_idx_case nocalls ctx func cenv cx bt /\
    (nocalls ==> int_calls_target bt = []) /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  rpt strip_tac >> Cases_on `EVERY pure_expr (target_indices bt)`
  >- (irule pop_nested_immutable_deploy_pure_sim >> metis_tac[]) >>
  irule pop_nested_immutable_deploy_impure_index_case >> metis_tac[]
QED
