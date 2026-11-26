(* Compile the raw blueprint argument at the actual child and header cuts. *)
Theory bodyCreateBlueprintRawArgsMods
Ancestors
  exprLowering compileEnv builtinCreate exprLoweringProps
  vyperAST venomInst pair
Libs pairLib

Theorem blueprint_raw_args_parts_mods:
  compile_create_blueprint_args compile_expr cenv T later [e] sa = ((dp,len),sb) ==>
  ?vv sm sv ss ptr su sn.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv later) vv sm = (sv,ss) /\
    unwrap_value cenv sv ss = (ptr,su) /\
    emit_op MLOAD [ptr] su = (len,sn) /\
    emit_op ADD [ptr; Lit 32w] sn = (dp,sb)
Proof
  simp[compile_create_blueprint_args_def,comp_bind_def,comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any))
QED
