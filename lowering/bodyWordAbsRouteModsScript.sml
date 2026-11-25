(* Assemble the forced operand and checked Abs suffix at the same cuts. *)
Theory bodyWordAbsRouteMods
Ancestors
  bodyWordAbsShapeMods bodyWordAbsPrefixMods bodyWordAbsSuccessPathMods
  bodyWordAbsBindMods bodyScalarStackVVMods exprSimUnopProps exprLoweringProps
  bodyFullPredsMods bodyFullPostsMods loweringPosts vyperAST compileEnv

Theorem word_abs_sim_mods:
  (!DF lo d ctx sh PG f sf cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es /\
    (!sa. ?a op sb. compile_expr cenv ty e sa = (StackValue a op,sb)) /\
    (!s tv t. eval_expr cx e s = (INL tv,t) ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,sh,PG,f,sf) cenv cx ty e es) /\
  bt = Abs /\
  (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a bt args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin a bt args) es
Proof
  strip_tac >> gvs[] >> drule_all_then strip_assume_tac word_abs_shape_mods >> gvs[] >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es /\
   expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!df l d pg src ts ctx sh f sf ce env ty st.
                 _ ==> expr_sim_full_mods _ _ _ _ e _ /\ _` irule >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  conj_asm1_tac
  >- (PURE_REWRITE_TAC [expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
      drule_all_then strip_assume_tac word_abs_prefix_run_mods >>
      irule word_abs_bind_mods >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_body_pre_mods _ _ _ _ e _` (irule_at Any) >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      irule abs_suffix_success_path >>
      qpat_assum `lookup_block _ _ = SOME bb` (irule_at Any) >> simp[] >>
      qexists_tac `x` >> simp[]) >>
  irule scalar_stack_vv_sim_full_mods >>
  simp[expr_type_def, post_value_type_word, is_word_type_def, compile_not_abs_stack] >>
  metis_tac[eval_expr_builtin_value]
QED
