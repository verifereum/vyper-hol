Theory bodyIntCallDefaultSliceConstRootsMods
Ancestors
  alist list option pair rich_list constSubst constSubstMods constSubstModsCorrect
  exprSimHypsDefs supportedExprTraverse vyperAST vyperInterpreter vyperTypeContract

(* The two folds compute different replacement values but insert the same keys. *)
Triviality qualified_module_const_key:
  !tops acc src id from.
    (MEM id (MAP FST acc) ==> MEM (src,id) (MAP FST from)) /\
    MEM id (MAP FST (module_consts_env tops acc)) ==>
    MEM (src,id) (MAP FST (module_consts_env_mods src tops from))
Proof
  ho_match_mp_tac module_consts_env_ind >>
  simp[module_consts_env_def, module_consts_env_mods_def, MEM_APPEND] >>
  rpt strip_tac >> first_x_assum irule >>
  simp[MEM_APPEND] >> metis_tac[]
QED

Triviality qualified_module_const_keep:
  !src tops acc key.
    MEM key (MAP FST acc) ==>
    MEM key (MAP FST (module_consts_env_mods src tops acc))
Proof
  ho_match_mp_tac module_consts_env_mods_ind >>
  simp[module_consts_env_mods_def, MEM_APPEND]
QED

Triviality ordered_const_key:
  !rest acc src id.
    MEM (src,id) (MAP FST acc) \/
    (?tops. MEM (src,tops) rest /\ MEM id (MAP FST (module_consts_env tops []))) ==>
    MEM (src,id) (MAP FST (consts_env_mods_acc rest acc))
Proof
  Induct >> simp[consts_env_mods_acc_def, FORALL_PROD] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[qualified_module_const_keep, qualified_module_const_key, MAP, MEM]
QED

Theorem checked_const_key:
  cx_const_name_mods mods key ==> IS_SOME (ALOOKUP (consts_env_mods mods) key)
Proof
  PairCases_on `key` >>
  simp[cx_const_name_mods_def, IS_SOME_EQ_NOT_NONE, ALOOKUP_NONE,
       consts_env_mods_def, consts_env_modules_order_eq] >>
  strip_tac >> irule ordered_const_key >> simp[MEM_constants_order] >>
  metis_tac[ALOOKUP_MEM]
QED

Theorem fixed_const_root_free:
  (!e. (!eenv. subst_consts_expr_mods eenv e = e) ==>
       ~supported_expr_exists (const_name_root_mods mods) e) /\
  (!t. (!eenv. subst_consts_btarget_mods eenv t = t) ==>
       ~supported_target_exists (const_name_root_mods mods) t) /\
  (!es. (!eenv. subst_consts_exprs_mods eenv es = es) ==>
        ~supported_exprs_exists (const_name_root_mods mods) es) /\
  (!d. (!eenv. subst_consts_opt_mods eenv d = d) ==>
       ~supported_opt_exists (const_name_root_mods mods) d) /\
  (!fs. (!eenv. subst_consts_fields_mods eenv fs = fs) ==>
        ~supported_fields_exists (const_name_root_mods mods) fs)
Proof
  ho_match_mp_tac fold_const_expr_ind >>
  simp[subst_consts_expr_mods_def, supported_expr_exists_def,
       const_name_root_mods_def, FORALL_AND_THM] >>
  rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!eenv. subst_consts_expr_mods eenv (TopLevelName _ ns) = _`
        (qspec_then `[(ns,Literal NoneT (BoolL F))]` mp_tac) >>
      PairCases_on `ns` >> simp[subst_consts_expr_mods_def, ALOOKUP_def])
QED

Theorem subst_const_roots_eliminated:
  (!key. cx_const_name_mods mods key ==> IS_SOME (ALOOKUP env key)) /\
  (!key rhs. ALOOKUP env key = SOME rhs ==>
     ~supported_expr_exists (const_name_root_mods mods) rhs) ==>
  (!e. ~supported_expr_exists (const_name_root_mods mods) (subst_consts_expr_mods env e)) /\
  (!t. ~supported_target_exists (const_name_root_mods mods) (subst_consts_btarget_mods env t)) /\
  (!es. ~supported_exprs_exists (const_name_root_mods mods) (subst_consts_exprs_mods env es)) /\
  (!d. ~supported_opt_exists (const_name_root_mods mods) (subst_consts_opt_mods env d)) /\
  (!fs. ~supported_fields_exists (const_name_root_mods mods) (subst_consts_fields_mods env fs))
Proof
  strip_tac >> ho_match_mp_tac fold_const_expr_ind >>
  simp[subst_consts_expr_mods_def, supported_expr_exists_def, const_name_root_mods_def] >>
  rpt gen_tac >> PairCases_on `ns` >>
  Cases_on `ALOOKUP env (ns0,ns1)` >>
  gvs[subst_consts_expr_mods_def, supported_expr_exists_def, const_name_root_mods_def] >>
  metis_tac[IS_SOME_DEF]
QED

Theorem intcall_default_slice_no_const_roots_mods:
  check_contract deploy layouts addr mods = SOME art /\
  ds = DROP n (subst_consts_exprs_mods (consts_env_mods mods) dflts) ==>
  ~supported_exprs_exists (const_name_root_mods mods) ds
Proof
  strip_tac >>
  `!key. cx_const_name_mods mods key ==> IS_SOME (ALOOKUP (consts_env_mods mods) key)` by
    simp[checked_const_key] >>
  `!key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==>
     ~supported_expr_exists (const_name_root_mods mods) rhs` by
    (drule checked_consts_env_mods_closed >>
     metis_tac[cj 1 fixed_const_root_free]) >>
  drule_all_then strip_assume_tac subst_const_roots_eliminated >>
  qpat_assum `!es. ~supported_exprs_exists _ (subst_consts_exprs_mods _ es)`
    (qspec_then `dflts` mp_tac) >>
  pure_rewrite_tac[supported_exprs_exists_every, EXISTS_MEM] >>
  metis_tac[MEM_DROP_IMP]
QED
