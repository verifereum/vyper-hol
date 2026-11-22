(* Request-prefix companion to bodyFullIf. *)
Theory s1PrefixIf
Ancestors
  s1PrefixPreds bodyFullIf s1PrefixDefs

Theorem compile_if_stmt_frag_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty c ss1 ss2
   es.
  (ctx_has_dalloca ctx /\ MEM func ctx.ctx_functions ==>
      !bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  expr_type c = BaseT BoolT /\
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (BaseT BoolT) c es /\
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (BaseT BoolT) c es /\
  (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  (!sa op sb.
       lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr c) sa =
         (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
  cs_mono (stmts_env cenv lctx ty ss1) /\
  cs_mono (stmts_env cenv lctx ty ss2) /\
  cs_mono (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss1)) /\
  cs_mono (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss2)) /\
  gas_shadow_compiles (lower_value compile_expr cenv (BaseT BoolT) c)
      (lower_value compile_expr (gas_shadow_env T cenv) (BaseT BoolT) (gas_shadow_expr c)) /\
  gas_shadow_compiles_env T (stmts_env cenv lctx ty ss1)
      (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss1)) /\
  gas_shadow_compiles_env T (stmts_env cenv lctx ty ss2)
      (stmts_env (gas_shadow_env T cenv) lctx ty (MAP gas_shadow_stmt ss2)) /\
  (!gs b es1.
       bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
         (INL (BoolV b), es1) ==>
       stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (stmts_env (gas_shadow_env T cenv) lctx ty
            (if b then MAP gas_shadow_stmt ss1 else MAP gas_shadow_stmt ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) /\
  (!gs b es1.
       bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
         (INL (BoolV b), es1) ==>
       stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (stmts_env (gas_shadow_env T cenv) lctx ty
            (if b then MAP gas_shadow_stmt ss1 else MAP gas_shadow_stmt ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (If c ss1 ss2))
      (stmt_env (gas_shadow_env T cenv) lctx ty
         (If (gas_shadow_expr c) (MAP gas_shadow_stmt ss1)
            (MAP gas_shadow_stmt ss2)))
      (eval_stmt cx (If c ss1 ss2)) es
Proof
  cheat
QED
