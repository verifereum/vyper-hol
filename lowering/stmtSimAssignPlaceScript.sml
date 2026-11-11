(*
 * Statement simulation: Assign to any place (#637, #851)
 *
 * t = e for a base target t of a value type: a local or a field or element
 * of one, a storage or transient variable or a field or element of one, or
 * a mapping's value.  The source evaluates e, then t's place, reads e's
 * value and writes it there (eval_stmt).  The lowering, in the same order,
 * evaluates e, computes t's pointer (compile_get_target_ptr, whose
 * simulation is targetPlaceSim's target_sim), unwraps e's value and stores
 * it at the pointer's location (placeStore).  An empty value of a type
 * with a length word compiles no code for e and stores a zero length word.
 *
 * The target's indices are pure (supported_target_pure).  Admitted, each
 * waiting on a later change outside this theory:
 *   assign_place_effectful_index_case — an index with effects, as
 *     targetPlaceSimCases' pop_nested_storage_effectful_sim;
 *   immutable_deploy_assign_case — an immutable written by the
 *     constructor, until immutable_alloca_sep and body_inv relate the
 *     constructor's immutables buffer to the source's immutables.
 *
 * TOP-LEVEL:
 *   compile_assign_place_case — t = e for every outcome
 *)

Theory stmtSimAssignPlace
Ancestors
  immutableAssignMetadata immutableAssignRepresentation immutableAssignStore
  immutableDeployAssignRestore immutableAssignCode immutableAssignEmpty
  immutableAssignCompose immutableAssignOpen stmtSimForced
  bodySim supportedTargets supportedDecls
  placeStore targetPlaceSimCases targetPlaceSim targetPlaceSimDefs
  stmtSimDefs exprSimHypsDefs exprSimDefs typedCopyDomain loweringPosts
  stmtLowering exprLowering compileEnv
  vyperInterpreter vyperState vyperTypeSystem
  venomState

Theorem compile_assign_place_case:
  !ctx func cx lctx RetQ cenv ty env tops bt e es dty.
    supported_target_pure tops bt /\
    type_place_target env bt = SOME (Type dty) /\
    type_widens_to env.type_defs (expr_type e) dty /\
    assignable_type env.type_defs (expr_type e) /\
    (lowered_value_type cenv e = expr_type e \/
     is_bytestring_type (expr_type e) /\
     is_bytestring_type (lowered_value_type cenv e) /\
     arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
    ((?s pv s1 sread v s2. eval_expr cx e s = (INL pv,s1) /\
                           read_result cx pv sread = (INL v,s2)) ==>
     target_case F ctx func cenv cx bt) /\
    ~immutable_root cx bt /\
    assign_alloc_ok cenv bt e /\
    target_indices_pre cenv cx env bt /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget bt) e))
      (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  cheat
QED

(* ADMITTED: an index with effects (see the header). *)
Theorem assign_place_effectful_index_case:
  !ctx func cx lctx RetQ cenv ty env tops bt e es dty.
    ~supported_target_pure tops bt /\
    type_place_target env bt = SOME (Type dty) /\
    type_widens_to env.type_defs (expr_type e) dty /\
    assignable_type env.type_defs (expr_type e) /\
    ((?s pv s1 sread v s2. eval_expr cx e s = (INL pv,s1) /\
                           read_result cx pv sread = (INL v,s2)) ==>
     target_case F ctx func cenv cx bt) /\
    ~immutable_root cx bt /\
    assign_alloc_ok cenv bt e /\
    target_indices_pre cenv cx env bt /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es /\ cenv.ce_target CapMcopy /\
    body_inv tops ctx cenv cx /\
    stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
    cenv.ce_func_mutability = build_func_mutability tops /\
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget bt) e))
      (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  cheat
QED

(* ADMITTED: an immutable written by the constructor (see the header).
   assignable_type excludes the empty struct, the one zero-size value type:
   its unwrap still emits an MLOAD/ISTORE that clobbers a neighbouring
   immutable (checked counterexample), and Vyper rejects empty structs. *)
Theorem immutable_deploy_assign_case:
  !ctx func cx lctx RetQ cenv ty env tops nsid e es ity.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    supported_immutable_type tops nsid = SOME ity /\
    type_place_target env (TopLevelNameTarget nsid) = SOME (Type ity) /\
    type_widens_to env.type_defs (expr_type e) ity /\
    assignable_type env.type_defs (expr_type e) /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  rpt gen_tac >> strip_tac >> PairCases_on `nsid` >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all immutable_assign_bare_global >> strip_tac >> gvs[] >>
  drule_all immutableDeployAssignFactsTheory.immutable_assign_target_layout >>
  disch_then (qspec_then `compile_expr` strip_assume_tac) >> gvs[] >>
  `?itv. evaluate_type (get_tenv cx) ity = SOME itv` by
    (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_immutables_consistent_def] >>
     qpat_x_assum `!src id ty. _ ==> IS_SOME _`
       (drule_then mp_tac) >>
     simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     PairCases_on `x` >> metis_tac[]) >>
  Cases_on `has_length_word (expr_type e) /\ is_empty_value_expr e`
  >- (irule immutable_assign_empty_stmt_frag >> metis_tac[]) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule_all immutable_assign_code_parts >> strip_tac >> gvs[] >>
  (irule forced_vv_then_stmt_outcome >>
  qexistsl_tac [
    `\raw ee t. vv_post ctx func cenv cx e es sa sm s0 ee raw vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts`, `e`,
    `\raw. do v <- read_result cx raw;
       p <- eval_target_place cx (TopLevelNameTarget (NONE,nsid1)); write_place cx p v od`] >>
  reverse conj_tac
  >- (conj_tac >- simp[Once evaluate_def] >>
      qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_vv_sim_def]) >>
      disch_then (qspecl_then [`sa`,`sm`,`vv`,`s0`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible]) >>
      simp[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `~block_is_terminated sb` by metis_tac[immutable_assign_loccode_open] >>
  `!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==>
     not_fresh_at sa x` by metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_imm_base] >>
  `supported_immutable_type tops (cenv.ce_module,nsid1) = SOME ity /\
   FLOOKUP cenv.ce_module_vars (cenv.ce_module,nsid1) = SOME (ImmutableLoc off) /\
   cenv.ce_module_var_type (cenv.ce_module,nsid1) = SOME ity` by simp[] >>
  `?fin q.
    (!tail. (do v <- read_result cx tv;
                p <- eval_target_place cx (TopLevelNameTarget (cenv.ce_module,nsid1)); write_place cx p v od)
       (ee with gas_obs := tail) = (INL (),fin with gas_obs := tail)) /\
    gas_marked_path F ctx func t 0 (OK q) /\
    stmt_post ctx func cx lctx cenv cenv sa sb es s0 (INL ()) fin q` by
    (irule immutable_assign_normal_continuation >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  qexistsl_tac [`INL ()`,`fin`,`OK q`] >> simp[] >>
  metis_tac[stmtSimDeclComposeTheory.stmt_post_end_gas_obs])
QED
