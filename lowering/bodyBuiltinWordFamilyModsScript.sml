(* Linked word-family selection, independent of the two unary route producers. *)
Theory bodyBuiltinWordFamilyMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyWordNegRouteMods bodyWordAbsRouteMods bodyWordWeiRouteMods
  bodyWordModOperandsMods bodyWordModSuffixMods
  bodyWordPowOperandsMods bodyWordPowSuffixMods bodyScalarStackVVMods
  bodyInvSplit exprSimHypsDefs vyperAST vyperTypeSystem list

val not_route = ``
  !mods exps DF lo d ctx shadow_ctx PG src tops func shadow_func cenv env cx ty a bt args es.
    bt = Not /\
    (builtin_args_length_ok bt (LENGTH args) ==>
      body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es``;

val rounding_route = ``
  !mods exps DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env cx ty a bt args es.
    (bt = Ceil \/ bt = Floor) /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a bt args) es``;

Theorem word_family_from_routes_mods:
  ^not_route ==> ^rounding_route ==>
  !mods exps cx ty bt es.
    (bt = Not \/ bt = Neg \/ bt = Abs \/ (?d. bt = AsWeiValue d) \/ bt = Ceil \/
     bt = Floor \/ bt = AddMod \/ bt = MulMod \/ bt = PowMod256) /\
    (builtin_args_length_ok bt (LENGTH es) ==> body_exprs_full_ok_mods mods exps cx es) ==>
    body_expr_full_ok_mods mods exps cx (Builtin ty bt es)
Proof
  disch_then (mk_asm "not_route") >> disch_then (mk_asm "rounding_route") >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  ONCE_REWRITE_TAC [body_expr_full_ok_mods_def] >> reverse conj_tac
  >- (qpat_x_assum `bt = Not \/ _` strip_assume_tac >> simp[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `bt = Not \/ _` strip_assume_tac >> gvs[]
  >- (asm "not_route" irule >> simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[])
  >- (irule word_neg_sim_mods >> simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[])
  >- (irule (REWRITE_RULE [scalar_stack_vv_sim_full_mods] word_abs_sim_mods) >>
      simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[])
  >- (irule word_wei_sim_mods >> simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[])
  >- (asm "rounding_route" irule >> simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[])
  >- (asm "rounding_route" irule >> simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[])
  >- (irule (REWRITE_RULE [modular_suffix_mods,scalar_stack_vv_sim_full_mods]
              modular_sim_from_suffix_mods) >>
      simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[])
  >- (irule (REWRITE_RULE [modular_suffix_mods,scalar_stack_vv_sim_full_mods]
              modular_sim_from_suffix_mods) >>
      simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  irule (MATCH_MP (MATCH_MP pow_mod256_sim_from_suffix_mods pow_mod256_suffix_mods)
                  scalar_stack_vv_sim_full_mods) >>
  simp[] >> qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]
QED
