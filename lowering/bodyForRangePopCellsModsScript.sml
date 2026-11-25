Theory bodyForRangePopCellsMods
Ancestors
  bodyBranchCellFrameMods bodyNormalHeadTailMods bodyFullPredsMods
  constSubstCorrect vyperTypeEnvExtension vyperTypeSystem vyperInterpreter
  vyperState finite_map

Theorem range_cells_static_cong[local]:
  env1.type_defs = env.type_defs /\
  env1.bare_globals = env.bare_globals /\
  env1.bare_global_assignable = env.bare_global_assignable /\
  env1.fn_sigs = env.fn_sigs /\ env1.toplevel_vtypes = env.toplevel_vtypes ==>
  (body_const_cells_agree_mods mods cx env1 es <=>
   body_const_cells_agree_mods mods cx env es)
Proof
  strip_tac >>
  simp[body_const_cells_agree_mods_def, checked_frame_context_def, frame_maps_def]
QED

(* Keep the incoming static environment even if the evaluated head stops
   the list. Only the success branch needs to replay the tail. *)
Theorem range_cells_typed_stmts[local]:
  !body env es raw pre env_b.
    body_const_cells_agree_mods mods cx env es /\
    type_stmts env ret_ty body = SOME env_b /\
    eval_stmts cx body es = (raw,pre) ==>
    body_const_cells_agree_mods mods cx env pre
Proof
  Induct >- simp[Once evaluate_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmts _ _ (_::_) = _` mp_tac >>
  simp[Once type_stmt_def, AllCaseEqs()] >>
  disch_then (qx_choose_then `env1` strip_assume_tac) >>
  Cases_on `eval_stmt cx h es` >>
  rename1 `eval_stmt cx h es = (res,mid)` >>
  drule_all_then assume_tac body_const_cells_agree_mods_stmt >>
  `body_const_cells_agree_mods mods cx env1 pre` by
    (qpat_x_assum `eval_stmts _ (_::_) _ = _` mp_tac >>
     Cases_on `res` >>
     simp[Once evaluate_def, ignore_bind_def, bind_def] >>
     strip_tac >> gvs[] >>
     first_x_assum irule >> conj_tac
     >- (qexists_tac `env_b` >> simp[]) >>
     qexistsl_tac [`mid`, `raw`] >> simp[]) >>
  drule_then strip_assume_tac type_stmt_env_preserved_static >>
  drule_all_then (fn th => fs[th]) range_cells_static_cong
QED

Theorem range_body_pop_cells_mods:
  !mods cx env es id fty tyv v ret_ty body env_b gs raw pre sc rest.
    body_const_cells_agree_mods mods cx env es /\
    type_stmts (extend_local env id fty F) ret_ty body = SOME env_b /\
    eval_stmts cx body
      ((es with scopes :=
          (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v;
                            popped := []|>)) :: es.scopes) with gas_obs := gs) = (raw,pre) /\
    pre.scopes = sc::rest ==>
    body_const_cells_agree_mods mods cx env (pre with scopes := rest)
Proof
  rpt gen_tac >> strip_tac >>
  `!st. body_const_cells_agree_mods mods cx (extend_local env id fty F) st <=>
        body_const_cells_agree_mods mods cx env st` by
    (gen_tac >> irule range_cells_static_cong >> simp[extend_local_def]) >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx _ entry` >>
  `body_const_cells_agree_mods mods cx (extend_local env id fty F) entry` by
    simp[Abbr `entry`] >>
  drule_all_then mp_tac range_cells_typed_stmts >> simp[]
QED
