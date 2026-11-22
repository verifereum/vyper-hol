Theory runtimeConstantSubstitutionProps
Ancestors
  constSubstCorrect constSubst vyperTypeContract whitelistCheckerConsts vyperAST alist list

Theorem subst_const_runtime_constant:
  runtime_constant_expr mods e /\
  (!id r. ALOOKUP env id = SOME r ==> constant_expr mods r) ==>
  runtime_constant_expr mods (subst_consts_expr env e)
Proof
  strip_tac >>
  `!ms exp. ms = mods /\ runtime_constant_expr ms exp ==>
    runtime_constant_expr ms (subst_consts_expr env exp)` suffices_by
    metis_tac[] >>
  `!src id ty. (declared_constant mods src id \/ declared_immutable mods src id) ==>
    runtime_constant_expr mods (subst_consts_expr env (TopLevelName ty (src,id)))` by
    (rpt gen_tac >> Cases_on `src` >>
     simp[subst_consts_expr_def, runtime_constant_expr_def] >>
     Cases_on `ALOOKUP env id` >> simp[runtime_constant_expr_def] >>
     metis_tac[constant_expr_runtime_constant]) >>
  `!e. bool_literal_expr e ==> bool_literal_expr (subst_consts_expr env e)` by
    (Cases >> simp[bool_literal_expr_def, subst_consts_expr_def]) >>
  `!es. EVERY (constant_expr mods) es ==>
    EVERY (constant_expr mods) (subst_consts_exprs env es)` by
    metis_tac[subst_consts_constant_expr] >>
  ho_match_mp_tac runtime_constant_expr_ind >>
  simp[runtime_constant_expr_def] >> rpt strip_tac >> gvs[] >>
  TRY (qpat_assum `!src id ty. _` irule >> simp[] >> NO_TAC) >>
  simp[subst_consts_expr_def, runtime_constant_expr_def,
    subst_consts_fields_maps] >>
  fs[subst_consts_exprs_map, EVERY_MAP, combinTheory.o_DEF, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP] >> res_tac >> fs[] >>
  metis_tac[]
QED
