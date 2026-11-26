(* Join the value and mapping simulations of the linked Subscript constructor. *)
Theory bodySubscriptCaseMods
Ancestors
  bodyFullPredsMods bodySubscriptArrayRoutesMods bodySubscriptValueBaseMods
  bodySubscriptMapCaseMods bodySubscriptMapRoutesMods bodyMapSubscriptStaticMods
  bodySubscriptTupleVVMods bodySubscriptValueReadMods exprLowering

Triviality map_place_shape:
  place_type cenv obj = MapPT kt vt ==>
  (?a id. obj = TopLevelName a id) \/ (?a b i. obj = Subscript a b i)
Proof
  Cases_on `obj` >> simp[place_type_def]
QED

(* The nested value-base supplier is nested_subscript_map_child_mods at
   obj = Subscript a b i. The map-result clause uses the child judgment
   directly at the base map precondition, without a value precondition. *)
Theorem body_subscript_case_full_mods:
  !mods exps cx ann obj idx.
    (!s'' res t s3 res' t'.
       eval_expr cx obj s'' = (INL res,t) /\
       (if subscript_reads_base cx obj idx then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_full_ok_mods mods exps cx idx) /\
    body_expr_full_ok_mods mods exps cx obj /\
    (!a b i kt vt DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       obj = Subscript a b i /\
       body_expr_full_ok_mods mods exps cx (Subscript a b i) /\
       contract_inv mods exps ctx cenv cx /\
       module_body_inv mods src tops cenv cx /\
       shadow_body_inv_mods mods exps ctx shadow_ctx /\
       body_const_cells_agree_mods mods cx env es /\
       expr_body_pre_mods mods cenv cx env (Subscript ann (Subscript a b i) idx) es /\
       place_type cenv (Subscript a b i) = MapPT kt vt ==>
       expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty (Subscript a b i) es) ==>
    body_expr_full_ok_mods mods exps cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >> simp[Once body_expr_full_ok_mods_def] >>
  conj_tac >- suspend "value" >>
  suspend "map"
QED

Resume body_subscript_case_full_mods[value]:
  rpt gen_tac >> strip_tac >>
  Cases_on `place_type cenv obj`
  >- suspend "map_leaf" >>
  drule_all_then strip_assume_tac subscript_val_base_cases_mods >> gvs[]
  >- (irule subscript_array_full_mods >> simp[] >>
      conj_tac >- (qexistsl [`bd`,`et`] >> simp[]) >>
      qexistsl [`env`,`exps`,`mods`,`src`,`tops`] >> asm_rewrite_tac[]) >>
  suspend "tuple"
QED

Resume body_subscript_case_full_mods[map_leaf]:
  drule_all_then strip_assume_tac (cj 2 map_subscript_static_mods) >>
  `expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty obj es` by
    (drule map_place_shape >> strip_tac
     >- (gvs[] >> PairCases_on `id` >> irule toplevel_map_sim_full_mods >> goal_assum (drule_at Any)) >>
     gvs[] >> first_x_assum irule >> simp[] >> conj_tac
     >- (qexistsl [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Subscript ann obj idx) es` by
    (irule subscript_map_leaf_from_reached_mods >> simp[] >>
     qexistsl [`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
     qpat_assum `!s r t s0 r0 t0. _ ==> body_expr_full_ok_mods _ _ _ _` mp_tac >> simp[]) >>
  simp[] >> irule subscript_noncopied_value_of_vv_mods >> simp[] >>
  qexistsl [`env`,`mods`] >> simp[] >> disj1_tac >> goal_assum (drule_at Any)
QED

Resume body_subscript_case_full_mods[tuple]:
  qpat_x_assum `TupleT tys = expr_type obj` (assume_tac o SYM) >>
  `expr_body_pre_mods mods cenv cx env obj es` by
    (drule_all subscript_tuple_pre_mods >> simp[]) >>
  qpat_assum `body_expr_full_ok_mods _ _ _ obj`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty obj es` by
    (qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                  _ ==> expr_sim_full_mods _ _ _ _ obj _ /\ _`
       (drule_all_then assume_tac) >>
     first_assum (MATCH_ACCEPT_TAC o CONJUNCT2 o SPEC_ALL)) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Subscript ann obj idx) es` by
    (irule subscript_tuple_vv_sim_full_mods >> simp[] >>
     qexistsl [`env`,`mods`] >> asm_rewrite_tac[]) >>
  simp[] >> irule subscript_noncopied_value_of_vv_mods >> simp[] >>
  qexistsl [`env`,`mods`] >> simp[] >> disj2_tac >> goal_assum (drule_at Any)
QED

Resume body_subscript_case_full_mods[map]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac (cj 1 map_subscript_static_mods) >>
  `expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty obj es` by
    (drule map_place_shape >> strip_tac
     >- (gvs[] >> PairCases_on `id` >> irule toplevel_map_sim_full_mods >> goal_assum (drule_at Any)) >>
     gvs[] >>
     qpat_x_assum `body_expr_full_ok_mods _ _ _ (Subscript _ _ _)`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!a b i DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                  _ ==> expr_map_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac
     >- (qexistsl [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  irule subscript_map_result_from_reached_mods >> simp[] >>
  qexistsl [`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
  qpat_assum `!s r t s0 r0 t0. _ ==> body_expr_full_ok_mods _ _ _ _` mp_tac >> simp[]
QED

Finalise body_subscript_case_full_mods
