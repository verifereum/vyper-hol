(* An elaborated offset is unchanged by linked constant substitution. *)
Theory createSizeBlueprintOffsetElabMods
Ancestors
  alist constSubst constSubstMods createSizeBlueprintOffsetKeyMods
  exprSimHypsDefs list option supportedExprTraverse vyperAST

Theorem linked_subst_unchanged[local]:
  (!env e. ~supported_expr_exists
      (\x. ?ty key. x = TopLevelName ty key /\ IS_SOME (ALOOKUP env key)) e ==>
    subst_consts_expr_mods env e = e) /\
  (!env t. ~supported_target_exists
      (\x. ?ty key. x = TopLevelName ty key /\ IS_SOME (ALOOKUP env key)) t ==>
    subst_consts_btarget_mods env t = t) /\
  (!env es. ~supported_exprs_exists
      (\x. ?ty key. x = TopLevelName ty key /\ IS_SOME (ALOOKUP env key)) es ==>
    subst_consts_exprs_mods env es = es) /\
  (!env opt. ~supported_opt_exists
      (\x. ?ty key. x = TopLevelName ty key /\ IS_SOME (ALOOKUP env key)) opt ==>
    subst_consts_opt_mods env opt = opt) /\
  (!env fs. ~supported_fields_exists
      (\x. ?ty key. x = TopLevelName ty key /\ IS_SOME (ALOOKUP env key)) fs ==>
    subst_consts_fields_mods env fs = fs)
Proof
  ho_match_mp_tac subst_consts_expr_mods_ind >>
  rw[subst_consts_expr_mods_def, supported_expr_exists_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem module_constant_name[local]:
  !tops acc id.
    MEM id (MAP FST acc) \/
      (?v e ty slot. MEM (VariableDecl v (Constant e) id ty slot) tops) ==>
    MEM id (MAP FST (module_consts_env tops acc))
Proof
  recInduct module_consts_env_ind >> rw[module_consts_env_def, MAP_APPEND] >>
  first_x_assum irule >> simp[MAP_APPEND] >> metis_tac[]
QED

Theorem blueprint_offset_subst_unchanged_mods:
  ALL_DISTINCT (MAP FST mods) /\
  ~supported_expr_exists (const_name_root_mods mods) e ==>
  subst_consts_expr_mods (consts_env_mods mods) e = e
Proof
  strip_tac >> irule (cj 1 linked_subst_unchanged) >> strip_tac >>
  qpat_assum `supported_expr_exists _ e`
    (mp_then Any (qspec_then `const_name_root_mods mods` mp_tac)
      (cj 1 supported_expr_exists_mono)) >>
  impl_tac >- (
    simp[const_name_root_mods_def, pairTheory.FORALL_PROD, IS_SOME_EXISTS] >>
    rpt strip_tac >> Cases_on `key` >>
    drule_then strip_assume_tac consts_env_mods_key >>
    gvs[const_name_root_mods_def, cx_const_name_mods_def] >> qexists `tops` >> conj_tac
    >- (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]) >>
    irule module_constant_name >> metis_tac[]
  ) >> simp[]
QED
