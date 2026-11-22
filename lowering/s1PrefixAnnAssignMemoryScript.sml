(* Request-prefix companion to bodyFullAnnAssignMemory. *)
Theory s1PrefixAnnAssignMemory
Ancestors
  s1PrefixPreds bodyFullAnnAssignMemory s1PrefixDefs

Theorem annassign_memory_prefix_execution:
  body_inv tops ctx cenv cx /\
  expr_sim_inv cenv cx env es /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP cenv.ce_vars id = NONE /\
  lookup_scopes id es.scopes = NONE /\
  type_widens_to env.type_defs (expr_type e) typ /\
  assignable_type env.type_defs typ /\
  stmt_exprs_ok cenv (AnnAssign id typ e) /\
  ~is_word_type typ /\
  0 < type_memory_bytes cenv typ /\
  (lowered_value_type cenv e = typ \/ is_bytestring_type typ \/
    has_length_word typ /\ is_empty_value_expr e) /\
  (lowered_value_type cenv e = expr_type e \/
    is_bytestring_type (expr_type e) /\
    is_bytestring_type (lowered_value_type cenv e) /\
    arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) /\
  (!sa ce r ty. declare_local cenv id typ sa = (ce,r) ==>
    body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty e es) ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AnnAssign id typ e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt (AnnAssign id typ e)))
    (eval_stmt cx (AnnAssign id typ e)) es
Proof
  cheat
QED
