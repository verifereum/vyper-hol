(* A successful reference fold fixes the constant cells that replay reads. *)
Theory vyperConstantFoldReplay
Ancestors
  list option finite_map vyperAST vyperState
  vyperTypeContract vyperTypeInitialState

Theorem constant_value_reference_congruence:
  (!mods ref e v.
    constant_expr mods e /\ constant_value mods ref e = SOME v ==>
    !a b.
      (!s id. declared_constant mods s id /\
        IS_SOME (FLOOKUP (get_source_immutables s ref) id) ==>
        FLOOKUP (get_source_immutables s a) id =
        FLOOKUP (get_source_immutables s b) id) ==>
      constant_value mods a e = constant_value mods b e) /\
  (!mods ref es vs.
    EVERY (constant_expr mods) es /\ constant_values mods ref es = SOME vs ==>
    !a b.
      (!s id. declared_constant mods s id /\
        IS_SOME (FLOOKUP (get_source_immutables s ref) id) ==>
        FLOOKUP (get_source_immutables s a) id =
        FLOOKUP (get_source_immutables s b) id) ==>
      constant_values mods a es = constant_values mods b es)
Proof
  ho_match_mp_tac constant_value_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[constant_expr_def, constant_value_def] >>
  rpt strip_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [AllCaseEqs()]) >>
  gvs[] >>
  rpt (qpat_x_assum `EVERY _ _ ==> _` mp_tac >>
       simp[EVERY_MEM] >> strip_tac) >>
  rpt (first_x_assum (qspecl_then [`a`,`b`] mp_tac)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  metis_tac[EVERY_MEM, IS_SOME_EXISTS]
QED

Theorem constants_fold_module_replay_present:
  !mods ref src ts acc.
    !env dst.
      constants_fold_module mods ref src ts acc = SOME env /\
      (!vis e id ty slot. MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
         constant_expr mods e) /\
      (!s id. declared_constant mods s id /\
         IS_SOME (FLOOKUP (get_source_immutables s ref) id) ==>
         FLOOKUP (get_source_immutables s dst) id =
         FLOOKUP (get_source_immutables s ref) id) ==>
      constants_fold_module mods dst src ts acc = SOME env
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rw[constants_fold_module_def] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [AllCaseEqs()]) >> gvs[] >>
  `constant_expr mods e` by metis_tac[] >>
  `constant_value mods (merge_constant_imms src acc dst) e =
   constant_value mods (merge_constant_imms src acc ref) e` by
    (irule (cj 1 constant_value_reference_congruence) >>
     reverse conj_tac >- simp[] >>
     qexistsl [`merge_constant_imms src acc ref`,`v`] >> simp[] >>
     rpt gen_tac >> strip_tac >>
     rename1 `declared_constant mods s query` >>
     Cases_on `s = src` >>
     gvs[merge_constant_imms_def, get_source_immutables_set_same,
         get_source_immutables_set_other, FLOOKUP_FUNION] >>
     Cases_on `FLOOKUP acc query` >> gvs[]) >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED
