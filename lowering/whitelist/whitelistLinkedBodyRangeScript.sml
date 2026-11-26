Theory whitelistLinkedBodyRange
Ancestors
  alist option integer vyperAST constSubst constSubstMods constSubstCorrect
  vyperImportRefs vyperTypeContract vyperTypeContractContext vyperTypeSystem
  whitelistCheckerDecls

(* Folding can introduce a byte literal, but never an integer literal. *)
Theorem fold_const_int_literal[local]:
  fold_const_expr e = Literal ty (IntL i) <=> e = Literal ty (IntL i)
Proof
  eq_tac >> strip_tac
  >- (`expr_type e = ty` by metis_tac[fold_const_expr_type, expr_type_def] >>
      mp_tac (Q.ISPECL [`SOME : int -> int option`, `NONE : int option`]
        (Q.GENL [`P`, `q`] fold_const_int_case)) >>
      simp[] >> Cases_on `e` >> gvs[expr_type_def] >>
      rename1 `Literal _ lit` >> Cases_on `lit` >> gvs[]) >>
  simp[fold_const_expr_def]
QED

(* For main-module names the two accumulators have the same lookup domain.
   Their values need only agree when the local lookup yields an integer literal. *)
Theorem subst_main_int_literal[local]:
  (!id. OPTREL (\u v. !ty i. u = Literal ty (IntL i) ==> v = Literal ty (IntL i))
     (ALOOKUP local_env id) (ALOOKUP linked_env (NONE,id))) /\
  subst_consts_expr local_env e = Literal ty (IntL i) ==>
  subst_consts_expr_mods linked_env e = Literal ty (IntL i)
Proof
  Cases_on `e` >> simp[subst_consts_expr_def, subst_consts_expr_mods_def] >>
  rename1 `TopLevelName aty key` >> PairCases_on `key` >>
  Cases_on `key0` >> simp[subst_consts_expr_def, subst_consts_expr_mods_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `key1` mp_tac) >>
  gvs[AllCaseEqs(), OPTREL_SOME]
QED

Theorem append_main_int_literals[local]:
  (!id. OPTREL (\u v. !ty i. u = Literal ty (IntL i) ==> v = Literal ty (IntL i))
     (ALOOKUP local_env id) (ALOOKUP linked_env (NONE,id))) ==>
  !id. OPTREL (\u v. !ty i. u = Literal ty (IntL i) ==> v = Literal ty (IntL i))
    (ALOOKUP (local_env ++ [(k,fold_const_expr (subst_consts_expr local_env e))]) id)
    (ALOOKUP (linked_env ++
      [((NONE,k),fold_const_expr (subst_consts_expr_mods linked_env e))]) (NONE,id))
Proof
  strip_tac >> gen_tac >> first_assum (qspec_then `id` assume_tac) >>
  simp[ALOOKUP_APPEND] >>
  Cases_on `ALOOKUP local_env id` >> gvs[OPTREL_SOME] >>
  simp[ALOOKUP_def] >> Cases_on `id = k` >> gvs[fold_const_int_literal] >>
  rpt strip_tac >> irule subst_main_int_literal >> qexists `local_env` >> simp[]
QED

Theorem module_main_int_literals[local]:
  !tops local_env linked_env.
    (!id. OPTREL (\u v. !ty i. u = Literal ty (IntL i) ==> v = Literal ty (IntL i))
       (ALOOKUP local_env id) (ALOOKUP linked_env (NONE,id))) ==>
    !id. OPTREL (\u v. !ty i. u = Literal ty (IntL i) ==> v = Literal ty (IntL i))
      (ALOOKUP (module_consts_env tops local_env) id)
      (ALOOKUP (module_consts_env_mods NONE tops linked_env) (NONE,id))
Proof
  Induct >> simp[module_consts_env_def, module_consts_env_mods_def] >>
  Cases_on `h` >> simp[module_consts_env_def, module_consts_env_mods_def] >>
  rename1 `VariableDecl _ mut _ _ _` >> Cases_on `mut` >>
  simp[module_consts_env_def, module_consts_env_mods_def,
       append_main_int_literals]
QED

Theorem module_imports_keep_main_lookup[local]:
  !tops m acc id.
    ALOOKUP (module_consts_env_mods (SOME m) tops acc) (NONE,id) =
    ALOOKUP acc (NONE,id)
Proof
  Induct >> simp[module_consts_env_mods_def] >>
  Cases_on `h` >> simp[module_consts_env_mods_def] >>
  rename1 `VariableDecl _ mut _ _ _` >> Cases_on `mut` >>
  simp[module_consts_env_mods_def, ALOOKUP_APPEND, ALOOKUP_def, SF ETA_ss]
QED

Theorem imports_before_main[local]:
  !imports acc tops.
    EVERY (IS_SOME o FST) imports ==>
    ?start. consts_env_mods_acc (imports ++ [(NONE,tops)]) acc =
              module_consts_env_mods NONE tops start /\
            !id. ALOOKUP start (NONE,id) = ALOOKUP acc (NONE,id)
Proof
  Induct >> simp[consts_env_mods_acc_def]
  >- (rpt gen_tac >> qexists `acc` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `h0` >> simp[consts_env_mods_acc_def] >>
  rpt strip_tac >> first_x_assum drule >>
  rename1 `module_consts_env_mods (SOME m) ts acc` >>
  disch_then (qspecl_then
    [`module_consts_env_mods (SOME m) ts acc`, `tops`] strip_assume_tac) >>
  qexists `start` >> simp[module_imports_keep_main_lookup]
QED

Theorem linked_main_int_literals[local]:
  ALL_DISTINCT (MAP FST mods) /\ ALOOKUP mods NONE = SOME tops ==>
  subst_consts_expr (module_consts_env tops []) e = Literal ty (IntL i) ==>
  subst_consts_expr_mods (consts_env_mods mods) e = Literal ty (IntL i)
Proof
  strip_tac >> drule_all constants_order_main_last >> strip_tac >>
  drule imports_before_main >> disch_then (qspecl_then [`[]`, `tops`] strip_assume_tac) >>
  simp[consts_env_mods_def, vyperInterpreterTheory.consts_env_modules_order_eq] >>
  strip_tac >> irule subst_main_int_literal >>
  qexists `module_consts_env tops []` >> simp[] >>
  irule module_main_int_literals >> simp[]
QED

Theorem imported_single_int_literal[local]:
  imported_expr_refs_ok e /\ subst_consts_expr env e = Literal ty (IntL i) ==>
  e = Literal ty (IntL i)
Proof
  Cases_on `e` >> simp[subst_consts_expr_def, imported_expr_refs_ok_def] >>
  rename1 `TopLevelName aty key` >> PairCases_on `key` >>
  Cases_on `key0` >> simp[subst_consts_expr_def]
QED

Theorem linked_checked_range_literals:
  check_contract mode layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  (src = NONE \/ imported_expr_refs_ok a /\ imported_expr_refs_ok b) /\
  type_stmt env ret (For x ty (Range a b) n lbody) = SOME env' /\
  IS_SOME (type_stmt env ret
    (For x ty (Range (subst_consts_expr_mods (consts_env_mods mods) a)
                      (subst_consts_expr_mods (consts_env_mods mods) b)) n body')) /\
  subst_consts_expr (module_consts_env tops []) a = Literal ta (IntL i) /\
  subst_consts_expr (module_consts_env tops []) b = Literal tb (IntL j) ==>
  supported_integer_type ty /\ i <= j /\ n = Num (j - i)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- metis_tac[type_stmt_for_range_integer_type] >>
  Cases_on `src`
  >- (drule check_contract_namespaces_ok >> strip_tac >>
      `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
      `subst_consts_expr_mods (consts_env_mods mods) a = Literal ta (IntL i)` by
        metis_tac[linked_main_int_literals] >>
      `subst_consts_expr_mods (consts_env_mods mods) b = Literal tb (IntL j)` by
        metis_tac[linked_main_int_literals] >>
      qpat_x_assum `IS_SOME _` (strip_assume_tac o REWRITE_RULE[IS_SOME_EXISTS]) >>
      qpat_x_assum `type_stmt _ _ (For _ _ (Range (subst_consts_expr_mods _ _) _) _ _) = _` mp_tac >>
      simp[] >> disch_tac >>
      drule type_stmt_for_range_literal_bounds >> simp[INT_LT_IMP_LE]) >>
  fs[] >>
  `a = Literal ta (IntL i)` by metis_tac[imported_single_int_literal] >>
  `b = Literal tb (IntL j)` by metis_tac[imported_single_int_literal] >>
  gvs[] >> drule type_stmt_for_range_literal_bounds >> simp[INT_LT_IMP_LE]
QED
