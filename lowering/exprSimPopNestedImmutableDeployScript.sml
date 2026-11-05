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

(* RESIDUAL, FALSE as stated (see below): pop on a member of an immutable in
   the constructor, which Python's checker accepts for a complex immutable
   (local.py skips the modification count when var_info is None).  The
   lowering loads and stores the length through the immutables buffer
   (compile_ptr_load/compile_ptr_store), and immutable_holds accepts the
   code pointer to the popped element, whose bytes the pop leaves in the
   buffer.  The proof also needs the constructor immutable invariant.
   The target's indices are lowered by compile_expr, so their judgments
   (target_idx_case) are a premise, as target_case_all takes them.  So
   are the constructor's compile env (ce_is_ctor: otherwise the length
   store is INVALID) and the root's declared type in ce_module_var_type,
   where compile_get_target_ptr reads the place type; body_inv gives the
   first, expr_sim_inv neither yet.

   FALSE as stated: the length store (compile_dynarray_pop's
   compile_ptr_store, an ISTORE into memory) breaks vv_post in two states
   the invariants allow:
   (a) two initialized immutables at overlapping offsets: a : struct{x:
       DynArray[uint256,1]} = {x:[7]} and b : uint256 = 1, both at
       ImmutableLoc 0.  Popping self.a.x writes 0 at offset 0; the source
       leaves b = 1, so immutables_rel fails for b.
   (b) a vs_allocas entry of s0 that is not an ALLOCA of func, say
       {0 |-> (0,64)} with no locals: immutable_alloca_sep clause 2 and
       stmt_state_rel separate the immutable region only from func's
       ALLOCAs, and the store changes mem_bytes_at 0 64, so vv_post's
       alloca frame fails.  (Execution records no such entry: the
       immutable base comes from compile_fixed_region_with_id's ASSIGN.)
   The fix: pairwise disjointness of the initialized immutables' regions
   (as immutable_section_layout gives) in expr_sim_inv or stmt_state_rel,
   and immutable_alloca_sep's clause 2 widened to every vs_allocas entry.
   The target walk, imm_target_walk in exprSimPopImmutableTarget, does
   not need either. *)
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

(* RESIDUAL, FALSE as stated: the expression-level case, with expr_body_pre
   alone, as the cut stated pop_nested_immutable_deploy_sim.  Admitted until
   expr_sim_inv carries cenv.ce_is_ctor <=> cx.in_deploy and the
   assignable immutables' declared types in ce_module_var_type, when it
   follows from pop_nested_immutable_deploy_sim (the indices' judgments
   from expr_sim_below, as compile_pop_nested_sim has them).
   Counterexample without the first: cx.in_deploy with
   cenv.ce_is_ctor = F, target self.s.a for an initialized immutable
   struct s whose DynArray field a is nonempty.  stmt_state_rel's
   immutables_rel then relates the data section, the length loads by
   DLOAD, and compile_ptr_store F emits INVALID for the length store, so
   the fragment aborts while the source pop returns its element.  Without
   the second, ce_module_var_type (src,id) = NONE leaves the target's place
   type NONE, and the lowering takes a uint256 element. *)
Theorem pop_nested_immutable_deploy_expr_case:
  !ctx func cenv cx env ann bt ty es src id.
    cx.in_deploy /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) ==>
    expr_vv_sim ctx func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED
