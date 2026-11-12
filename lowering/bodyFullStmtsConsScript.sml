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

(* Notes for the proof (may be ignored):
   - A pre-horizon proof of this composition, over a generic shadow
     statement with two shadow premises, is in git at 53fe3b2d9
     (lowering/bodyFullStmtsConsScript.sml).  Under the horizon its
     gas_outcome_full_bind_lands step no longer fits: the tail's input
     block is guarded by every horizon valid for the head's end trace.
     bodyFullIf's compile_if_stmt_frag_full composes the same way through
     gas_outcome_full_bind_all, reading H-free facts of the midpoint at
     storage_trace_horizon mid.storage_trace.
   - The shadow facts the pre-horizon proof took as premises follow from
     gas_shadow_terminated (bodyFullShared) and from gas_shadow_compiles of
     stmt_env (gas_shadow_compiles_bind, gas_shadow_compiles_declare_stmt_local,
     gas_shadow_compile_stmt).
   - dead_lo_ok depends on the environment only through ce_is_ctor, which
     cenv_top_ext preserves (cenv_top_ext_is_ctor). *)
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
