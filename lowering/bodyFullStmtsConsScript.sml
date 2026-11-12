(*
 * The statement-list cons case of the full body induction, over the
 * finite-horizon joint judgment: the head's joint fragment and the tail's,
 * composed through one source/memory/pointer witness, the head's landing
 * state feeding the tail's entry.
 *
 * TOP-LEVEL:
 *   stmt_frag_full_cons_env -- body_stmts_cons_case_full's composition
 *)
Theory bodyFullStmtsCons
Ancestors
  bodySimFull gasShadow loweringPosts vyperInterpreter vyperState list

Theorem stmt_frag_full_cons_env:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty
   stmt ss es.
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty stmt)
      (stmt_env cenv lctx ty (gas_shadow_stmt stmt))
      (eval_stmt cx stmt) es /\
    (!gs es1 c sa sm.
       eval_stmt cx stmt (es with gas_obs := gs) = (INL (), es1) /\
       stmt_env cenv lctx ty stmt sa = (c, sm) /\
       cenv_top_ext cenv c es1.scopes ==>
       stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cx lctx RetQ c
         (stmts_env c lctx ty ss)
         (stmts_env c lctx ty (MAP gas_shadow_stmt ss))
         (eval_stmts cx ss) es1) ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ty (stmt::ss))
      (stmts_env cenv lctx ty (MAP gas_shadow_stmt (stmt::ss)))
      (eval_stmts cx (stmt::ss)) es
Proof
  cheat
QED
