(* Owner-approved residue: the target-walk frame does not preserve dead
   popped storage/transient slots after an effectful RHS. *)
Theory assignPlaceEffectfulRhsResidue
Ancestors
  bodySim targetPlaceSim stmtSimDefs exprSimHypsDefs
  stmtLowering exprLowering compileEnv vyperInterpreter vyperTypeSystem

Theorem assign_place_effectful_rhs_residue:
  !ctx func cx lctx RetQ cenv ty env bt e es dty.
    ~expr_can_mutate cenv (target_to_expr bt) /\
    cenv.ce_func_mutability = build_func_mutability (cx_tops cx) /\
    (!vis mut nr rr fn args dflts ret body.
       MEM (FunctionDecl vis mut nr rr fn args dflts ret body) (cx_tops cx) ==>
       function_mutability_ok [(NONE, cx_tops cx)] vis mut nr dflts body) /\
    get_module_code cx NONE = SOME (cx_tops cx) /\
    EVERY (\c. FST c = NONE) (int_calls_target bt) /\
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
    acyclic_struct_metadata cenv.ce_struct_fields /\
    expr_has_effect e ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget bt) e))
      (eval_stmt cx (Assign (BaseTarget bt) e)) es
Proof
  cheat
QED
