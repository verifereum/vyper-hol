(* Finish the non-reading array route with the reached immutable selector. *)
Theory bodySubscriptArrayUnframedMods
Ancestors
  bodySubscriptArrayUnframedDispatchMods bodyArrayReachedImmutableMods
  bodySubscriptArrayRouteDefsMods bodyFullPostsMods vyperInterpreter vyperAST

Theorem subscript_array_unframed_full_mods:
  !mods exps cx ann obj idx DF lo d PG src tops ctx shadow_ctx func shadow_func
   cenv env ty es et bd.
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  subscript_array_unframed_case_mods cenv cx obj idx et bd ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >>
  irule subscript_array_unframed_dispatch_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`bd`,`env`,`et`,`exps`,`mods`,`src`,`tops`] >>
  asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
  drule_all_then ACCEPT_TAC array_reached_immutable_select_mods
QED
