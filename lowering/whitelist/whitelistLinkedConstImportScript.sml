(* Properties of the local constant replacements of an imported module. *)
Theory whitelistLinkedConstImport
Ancestors
  constSubstCorrect vyperImportRefsProps vyperImportRefs
  vyperTypeContract constSubst vyperAST alist list pair

Triviality imported_constant_syntax:
  (!e. constant_expr mods e /\ imported_expr_refs_ok e ==>
       const_local_refs e = [] /\ imported_expr_refs_ok (fold_const_expr e)) /\
  (!es. EVERY (constant_expr mods) es /\ imported_exprs_refs_ok es ==>
        const_local_exprs es = [] /\ imported_exprs_refs_ok (fold_const_exprs es)) /\
  (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ imported_field_refs_ok fs ==>
        const_local_fields fs = [] /\ imported_field_refs_ok (fold_const_fields fs))
Proof
  ho_match_mp_tac const_local_refs_ind >>
  simp[constant_expr_def, imported_expr_refs_ok_def, const_local_refs_def,
       fold_const_expr_def, SF ETA_ss] >>
  rpt strip_tac >> gvs[]
  >- (rename1 `FST ns <> NONE` >> PairCases_on `ns` >>
      Cases_on `ns0` >> gvs[const_local_refs_def])
  >> rename1 `fold_const_builtin ty bi args` >>
  Cases_on `bi` >> gvs[fold_const_builtin_def, imported_expr_refs_ok_def] >>
  Cases_on `args` >> gvs[imported_expr_refs_ok_def] >>
  Cases_on `t` >> gvs[imported_expr_refs_ok_def] >>
  Cases_on `h` >> gvs[imported_expr_refs_ok_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >> gvs[imported_expr_refs_ok_def]
QED

Triviality module_consts_env_imported_acc:
  !decls acc.
    (!vis e id ty slot. MEM (VariableDecl vis (Constant e) id ty slot) decls ==>
        constant_expr mods e /\ imported_expr_refs_ok e /\ P (fold_const_expr e)) /\
    EVERY (P o SND) acc ==>
    EVERY (P o SND) (module_consts_env decls acc)
Proof
  Induct >> simp[module_consts_env_def] >>
  Cases_on `h` >> simp[module_consts_env_def] >>
  TRY (first_assum ACCEPT_TAC) >>
  rename1 `VariableDecl vis mut id ty slot` >>
  Cases_on `mut` >> simp[module_consts_env_def] >>
  TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >> first_x_assum irule >> simp[EVERY_APPEND] >>
  rename1 `VariableDecl vis (Constant e) id ty slot` >>
  `constant_expr mods e /\ imported_expr_refs_ok e /\ P (fold_const_expr e)`
    by metis_tac[] >>
  conj_tac >- metis_tac[] >>
  `const_local_refs e = []` by metis_tac[imported_constant_syntax] >>
  `subst_consts_expr acc e = e` by metis_tac[const_closed_subst] >> simp[]
QED

Theorem imported_const_replacement_facts:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods (SOME s) = SOME tops /\
  MEM (id,r) (module_consts_env tops []) ==>
  constant_expr mods r /\ const_local_refs r = [] /\
  well_typed_expr (artifact_env art mods (SOME s)) r /\
  imported_expr_refs_ok r
Proof
  strip_tac >>
  `EVERY imported_toplevel_refs_ok tops`
    by metis_tac[ALOOKUP_MEM, check_contract_imported_toplevel_refs_ok] >>
  `!vis e id ty slot. MEM (VariableDecl vis (Constant e) id ty slot) tops ==>
     constant_expr mods e /\ imported_expr_refs_ok e /\
     constant_expr mods (fold_const_expr e) /\
     const_local_refs (fold_const_expr e) = [] /\
     well_typed_expr (artifact_env art mods (SOME s)) (fold_const_expr e) /\
     imported_expr_refs_ok (fold_const_expr e)` by
    (rpt gen_tac >> strip_tac >> drule_all checked_const_decl_typed >>
     strip_tac >>
     `imported_expr_refs_ok e` by
       (gvs[EVERY_MEM] >> first_x_assum drule >>
        simp[imported_toplevel_refs_ok_def]) >>
     `const_local_refs e = [] /\ imported_expr_refs_ok (fold_const_expr e)`
       by metis_tac[imported_constant_syntax] >>
     simp[fold_const_expr_constant, fold_const_expr_local_closed,
          fold_const_expr_typed]) >>
  qmatch_goalsub_abbrev_tac `well_typed_expr env r` >>
  `EVERY ((\e. constant_expr mods e /\ const_local_refs e = [] /\
                well_typed_expr env e /\ imported_expr_refs_ok e) o SND)
         (module_consts_env tops [])` by
    (irule module_consts_env_imported_acc >> simp[] >>
     qexists_tac `mods` >> simp[Abbr `env`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `EVERY _ (module_consts_env _ _)` mp_tac >>
  simp[EVERY_MEM] >> disch_then drule >> simp[]
QED
