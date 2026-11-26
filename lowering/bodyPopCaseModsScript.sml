(* Compose the linked target walk, the reached Pop suffix and the result read. *)
Theory bodyPopCaseMods
Ancestors
  bodyFullPredsMods bodyPopInputsMods bodyPopBindMods bodyPopSuffixMods
  bodyPopReadMods bodyWritePlaceRunMods

Theorem body_pop_case_full_mods:
  !mods exps cx ann bt.
    body_base_target_full_ok_mods mods exps cx bt ==>
    body_expr_full_ok_mods mods exps cx (Pop ann bt)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_full_ok_mods_def] >>
  qx_genl_tac [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,`func`,
    `shadow_func`,`cenv`,`env`,`ty`,`es`] >> strip_tac >>
  drule_then strip_assume_tac pop_target_inputs_mods >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT ann (Dynamic cap)))` >>
  `write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx env bt es` by
    (irule write_target_place_run_mods >>
     rpt (first_assum (irule_at Any)) >> simp[]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Pop ann bt) es` by
    (irule pop_vv_from_place_suffix_mods >>
     rpt (first_assum (irule_at Any)) >>
     rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule pop_place_suffix_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Pop _ _) _` (irule_at Any) >>
     qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
     qpat_assum `compile_expr _ _ (Pop _ _) _ = _` (irule_at Any) >>
     qpat_assum `write_target_entry_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexistsl [`marks`,`cap`] >> asm_simp_tac bool_ss []) >>
  simp[] >> irule pop_value_from_vv_mods >> simp[] >>
  qexistsl [`env`,`mods`] >> simp[]
QED
