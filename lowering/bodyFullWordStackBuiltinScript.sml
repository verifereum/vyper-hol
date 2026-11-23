(* Introduce a full body judgment from a guarded word-valued stack simulation. *)
Theory bodyFullWordStackBuiltin
Ancestors
  bodyFullPreds bodyFullExprGeneric exprLoweringProps loweringPosts
  exprLowering compileEnv vyperInterpreter vyperAST vyperTypeSystem

Theorem word_stack_builtin_body_full_intro:
  !cx ann bi args.
    (!t n. bi <> MakeArray t n) /\
    (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_body_pre cenv cx env (Builtin ann bi args) es ==>
      is_word_type (post_value_type cenv (Builtin ann bi args)) /\
      (!sa. ?tp op sb.
        compile_expr cenv ty (Builtin ann bi args) sa = (StackValue tp op,sb)) /\
      expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty (Builtin ann bi args) es) ==>
    body_expr_full_ok cx (Builtin ann bi args)
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac [body_expr_full_ok_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es. _`
        (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,
                      `shadow_func`,`cenv`,`env`,`ty`,`es`] mp_tac) >>
      simp[] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      irule expr_vv_sim_stack_full >>
      simp[post_value_type_word] >>
      metis_tac[eval_expr_builtin_value])
  >- (simp[])
QED
