(* Compose the linked value simulation for Not with its stack-value boundary. *)
Theory bodyWordNotComposeMods
Ancestors
  bodyScalarStackVVMods exprSimUnopProps exprSimHypsDefs
  vyperInterpreter vyperTypeSystem vyperAST compileEnv list


Theorem word_not_vv_from_value_mods:
  (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
     (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                SOME tvt ==> type_memory_size tvt = 0) /\
     expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
       cenv cx ty e es /\
     (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
     (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
       expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty e es) ==>
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty a args es.
    is_word_type (post_value_type cenv (Builtin a Not args)) /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a Not args) es /\
    (!sa. ?t op sb. compile_expr cenv ty (Builtin a Not args) sa =
                 (StackValue t op,sb)) /\
    (!s tv t. eval_expr cx (Builtin a Not args) s = (INL tv,t) ==>
       ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a Not args) es
Proof
  rpt strip_tac >> irule scalar_stack_vv_sim_full_mods >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
