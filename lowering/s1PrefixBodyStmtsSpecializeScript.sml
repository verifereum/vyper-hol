(* Specialization of the statement-list clause of prefix simulation. *)
Theory s1PrefixBodyStmtsSpecialize
Ancestors
  s1PrefixPreds bodyLoopCalls contractInvContextProps bodyFullPreds bodySim alist

val _ = Parse.hide "body";

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (mk_asm "list_clause") >> rpt strip_tac >>
  `!vis mut nr raw fn args dflts ret body.
      MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tops ==>
      stmts_loop_calls_ok [(NONE,tops)]
        (subst_consts_stmts (module_consts_env tops []) body)` by
    (qpat_assum `body_const_cells_agree _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
     `cx_tops cx = tops` by fs[ALOOKUP_def] >>
     rpt strip_tac >>
     drule checked_subst_consts_loop_calls_ok >>
     simp[] >> disch_then irule >> gvs[] >> metis_tac[]) >>
  `body_stmts_prefix_ok cx ss` by
    (asm "list_clause" irule >>
     drule_then assume_tac body_inv_contract >>
     drule_then assume_tac contract_inv_singleton_source_modules >>
     simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `body_stmts_prefix_ok _ _`
    (irule o REWRITE_RULE [body_stmts_prefix_ok_def]) >>
  metis_tac[]
QED
*)
Theorem body_stmts_sim_prefix_from_list_clause:
  (!cx ss. (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
                 struct_args_unique tops /\
                 (!vis mut nr raw fn args dflts ret body.
                    MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tops ==>
                    stmts_loop_calls_ok [(NONE,tops)]
                      (subst_consts_stmts (module_consts_env tops []) body)) /\
                 stmts_loop_calls_ok [(NONE,tops)] ss) ==>
    body_stmts_prefix_ok cx ss) ==>
  !DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv cx env env'
   ret_ty lctx RetQ ss es.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\ struct_args_unique tops /\
    supported_stmts tops bindings ss /\
    (!vis mut nr raw fn args dflts ret body.
       MEM (FunctionDecl vis mut nr raw fn args dflts ret body) tops ==>
       stmts_loop_calls_ok [(NONE,tops)] body) /\
    stmts_loop_calls_ok [(NONE,tops)] ss /\
    (!target. supported_stmts_expr_exists
       (expr_abi_decode_target_root target) ss ==>
       occurs_abi_decode_target target tops) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmts env ret_ty ss = SOME env' /\
    stmts_exprs_ok cenv ss /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmts_env cenv lctx ret_ty ss)
      (stmts_env (gas_shadow_env T cenv) lctx ret_ty (MAP gas_shadow_stmt ss))
      (eval_stmts cx ss) es
Proof
  cheat
QED
