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

(* ADMITTED: an immutable written by the constructor (see the header). *)
Theorem immutable_deploy_assign_case:
  !ctx func cx lctx RetQ cenv ty env tops nsid e es ity.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    supported_immutable_type tops nsid = SOME ity /\
    type_place_target env (TopLevelNameTarget nsid) = SOME (Type ity) /\
    type_widens_to env.type_defs (expr_type e) ity /\
    expr_vv_sim ctx func cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e))
      (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nsid)) e)) es
Proof
  cheat
QED
