Theory vyperImportRefsProps
Ancestors
  vyperImportRefs vyperTypeContract vyperTypeContractContext
  vyperAST vyperContext vyperInterpreter vyperABIEntries
  constSubstMods constSubst list alist pair

Theorem check_contract_main_module_present:
  check_contract deploy layouts addr mods = SOME art ==>
  IS_SOME (ALOOKUP mods NONE)
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def]
QED

Theorem check_contract_imported_toplevel_refs_ok:
  check_contract deploy layouts addr mods = SOME art /\ MEM (SOME src,tls) mods ==>
  EVERY imported_toplevel_refs_ok tls
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, EVERY_MEM, FORALL_PROD] >>
  strip_tac >>
  qpat_x_assum `!src tls. MEM (src,tls) mods ==> ALL_DISTINCT _ /\ _`
    (qspecl_then [`SOME src`,`tls`] mp_tac) >> simp[]
QED

Theorem check_contract_module_external_method_ids_distinct:
  check_contract deploy layouts addr mods = SOME art /\ MEM (src,tls) mods ==>
  ALL_DISTINCT (abi_external_method_ids (type_env tls) tls)
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, EVERY_MEM, FORALL_PROD] >>
  strip_tac >>
  qpat_x_assum `!src tls. MEM (src,tls) mods ==> ALL_DISTINCT _ /\ _`
    (qspecl_then [`src`,`tls`] mp_tac) >> simp[]
QED

Triviality fold_const_builtin_imported_refs_ok:
  imported_type_refs_ok ty /\ imported_builtin_refs_ok bi /\ imported_exprs_refs_ok args ==>
  imported_expr_refs_ok (fold_const_builtin ty bi args)
Proof
  strip_tac >>
  Cases_on `bi` >> simp[fold_const_builtin_def, imported_expr_refs_ok_def] >>
  Cases_on `args` >> simp[imported_expr_refs_ok_def] >>
  Cases_on `t` >> simp[imported_expr_refs_ok_def] >>
  Cases_on `h` >> simp[imported_expr_refs_ok_def] >>
  rename1 `Literal _ lit` >> Cases_on `lit` >> simp[imported_expr_refs_ok_def]
QED

Triviality fold_const_imported_refs_ok:
  (!e. imported_expr_refs_ok e ==> imported_expr_refs_ok (fold_const_expr e)) /\
  (!t. imported_base_target_refs_ok t ==>
       imported_base_target_refs_ok (fold_const_btarget t)) /\
  (!es. imported_exprs_refs_ok es ==> imported_exprs_refs_ok (fold_const_exprs es)) /\
  (!opt. imported_optional_expr_refs_ok opt ==>
         imported_optional_expr_refs_ok (fold_const_opt opt)) /\
  (!fs. imported_field_refs_ok fs ==> imported_field_refs_ok (fold_const_fields fs))
Proof
  ho_match_mp_tac fold_const_expr_ind >>
  simp[fold_const_expr_def, imported_expr_refs_ok_def] >>
  metis_tac[fold_const_builtin_imported_refs_ok]
QED

Triviality subst_consts_expr_imported_refs_ok:
  (!env e.
     (!id replacement. FST id <> NONE /\ ALOOKUP env id = SOME replacement ==>
                       imported_expr_refs_ok replacement) ==>
     imported_expr_refs_ok e ==> imported_expr_refs_ok (subst_consts_expr_mods env e)) /\
  (!env t.
     (!id replacement. FST id <> NONE /\ ALOOKUP env id = SOME replacement ==>
                       imported_expr_refs_ok replacement) ==>
     imported_base_target_refs_ok t ==>
     imported_base_target_refs_ok (subst_consts_btarget_mods env t)) /\
  (!env es.
     (!id replacement. FST id <> NONE /\ ALOOKUP env id = SOME replacement ==>
                       imported_expr_refs_ok replacement) ==>
     imported_exprs_refs_ok es ==> imported_exprs_refs_ok (subst_consts_exprs_mods env es)) /\
  (!env opt.
     (!id replacement. FST id <> NONE /\ ALOOKUP env id = SOME replacement ==>
                       imported_expr_refs_ok replacement) ==>
     imported_optional_expr_refs_ok opt ==>
     imported_optional_expr_refs_ok (subst_consts_opt_mods env opt)) /\
  (!env fs.
     (!id replacement. FST id <> NONE /\ ALOOKUP env id = SOME replacement ==>
                       imported_expr_refs_ok replacement) ==>
     imported_field_refs_ok fs ==> imported_field_refs_ok (subst_consts_fields_mods env fs))
Proof
  ho_match_mp_tac subst_consts_expr_mods_ind >>
  simp[subst_consts_expr_mods_def, imported_expr_refs_ok_def] >>
  rpt strip_tac
  >~ [`ALOOKUP _ (_,_)`]
  >- (rename1 `ALOOKUP constants (source,name)` >>
      Cases_on `ALOOKUP constants (source,name)` >>
      simp[imported_expr_refs_ok_def] >>
      qpat_x_assum `!key replacement. _`
        (qspec_then `(source,name)` mp_tac) >>
      simp[])
  (* Simplify each structural IH with the entire lookup premise. *)
  >> qpat_assum `!key replacement. _`
       (fn lookup_ok => fs[EQT_INTRO lookup_ok])
QED

Triviality imported_constant_lookup:
  EVERY (\(id,e). FST id <> NONE ==> imported_expr_refs_ok e) env /\
  FST id <> NONE /\ ALOOKUP env id = SOME e ==>
  imported_expr_refs_ok e
Proof
  Cases_on `id` >> simp[EVERY_MEM, FORALL_PROD] >>
  rpt strip_tac >> drule ALOOKUP_MEM >> disch_tac >>
  qpat_assum `!src name value. _` drule >> simp[]
QED

Triviality module_consts_env_imported_refs_ok:
  !tls src env.
    (src <> NONE ==> EVERY imported_toplevel_refs_ok tls) /\
    EVERY (\(id,e). FST id <> NONE ==> imported_expr_refs_ok e) env ==>
    EVERY (\(id,e). FST id <> NONE ==> imported_expr_refs_ok e)
      (module_consts_env_mods src tls env)
Proof
  Induct >> simp[module_consts_env_mods_def] >>
  Cases_on `h` >> simp[module_consts_env_mods_def] >>
  rename1 `VariableDecl vis mut name ty slot` >>
  Cases_on `mut` >> simp[module_consts_env_mods_def] >>
  rpt strip_tac >>
  qpat_assum `!src env. _ ==> EVERY _ (module_consts_env_mods src _ env)` irule >>
  simp[EVERY_APPEND] >> rpt strip_tac >>
  irule (CONJUNCT1 fold_const_imported_refs_ok) >>
  irule (CONJUNCT1 subst_consts_expr_imported_refs_ok) >>
  fs[imported_toplevel_refs_ok_def] >>
  rpt strip_tac >> drule_all imported_constant_lookup >> simp[]
QED

Triviality consts_env_acc_imported_refs_ok:
  !mods env.
    EVERY (\(src,tls). src <> NONE ==> EVERY imported_toplevel_refs_ok tls) mods /\
    EVERY (\(id,e). FST id <> NONE ==> imported_expr_refs_ok e) env ==>
    EVERY (\(id,e). FST id <> NONE ==> imported_expr_refs_ok e)
      (consts_env_mods_acc mods env)
Proof
  Induct >> simp[consts_env_mods_acc_def] >>
  Cases_on `h` >> simp[consts_env_mods_acc_def] >>
  rpt strip_tac >>
  qpat_assum `!env. _ ==> EVERY _ (consts_env_mods_acc _ env)` irule >>
  simp[] >> irule module_consts_env_imported_refs_ok >> simp[]
QED

Triviality check_contract_const_env_imported_refs_ok:
  check_contract deploy layouts addr mods = SOME art /\ FST id <> NONE /\
  ALOOKUP (consts_env_mods mods) id = SOME e ==>
  imported_expr_refs_ok e
Proof
  strip_tac >>
  `EVERY (\(key,rhs). FST key <> NONE ==> imported_expr_refs_ok rhs)
         (consts_env_mods mods)` by
    (simp[consts_env_mods_def, consts_env_modules_order_eq] >>
     irule consts_env_acc_imported_refs_ok >>
     simp[] >> once_rewrite_tac[EVERY_MEM] >>
     simp[FORALL_PROD, MEM_constants_order] >>
     Cases >> simp[] >> rpt strip_tac >>
     drule_all check_contract_imported_toplevel_refs_ok >> simp[]) >>
  drule_all imported_constant_lookup >> simp[]
QED

Triviality subst_consts_target_imported_refs_ok:
  (!env t.
    (!id e. FST id <> NONE /\ ALOOKUP env id = SOME e ==> imported_expr_refs_ok e) ==>
    imported_target_refs_ok t ==> imported_target_refs_ok (subst_consts_target_mods env t)) /\
  (!env ts.
    (!id e. FST id <> NONE /\ ALOOKUP env id = SOME e ==> imported_expr_refs_ok e) ==>
    imported_targets_refs_ok ts ==> imported_targets_refs_ok (subst_consts_targets_mods env ts))
Proof
  ho_match_mp_tac subst_consts_target_mods_ind >>
  simp[subst_consts_target_mods_def, imported_target_refs_ok_def] >>
  rpt strip_tac >>
  qpat_assum `!key value. FST key <> NONE /\ ALOOKUP _ key = SOME value ==> _`
    (fn lookup_ok =>
      fs[EQT_INTRO lookup_ok, CONJUNCT1 (CONJUNCT2 subst_consts_expr_imported_refs_ok)])
QED

Triviality subst_consts_stmt_imported_refs_ok:
  (!env s.
    (!id e. FST id <> NONE /\ ALOOKUP env id = SOME e ==> imported_expr_refs_ok e) ==>
    imported_stmt_refs_ok s ==> imported_stmt_refs_ok (subst_consts_stmt_mods env s)) /\
  (!env ss.
    (!id e. FST id <> NONE /\ ALOOKUP env id = SOME e ==> imported_expr_refs_ok e) ==>
    imported_stmts_refs_ok ss ==> imported_stmts_refs_ok (subst_consts_stmts_mods env ss))
Proof
  let
    fun refs_simp rules =
      qpat_assum `!key value. FST key <> NONE /\ ALOOKUP _ key = SOME value ==> _`
        (fn lookup_ok => fs (EQT_INTRO lookup_ok :: rules))
    val expr_ok = CONJUNCT1 subst_consts_expr_imported_refs_ok
    val custom_error_case =
      rename1 `subst_consts_error_mods constants err` >> Cases_on `err` >>
      refs_simp [subst_consts_error_mods_def, imported_error_refs_ok_def,
                 subst_consts_expr_imported_refs_ok]
  in
    ho_match_mp_tac subst_consts_stmt_mods_ind >>
    simp[subst_consts_stmt_mods_def, imported_stmt_refs_ok_def] >>
    rpt strip_tac
    >~ [`subst_consts_iter_mods _ _`]
    >- (rename1 `subst_consts_iter_mods constants iter` >> Cases_on `iter` >>
        refs_simp [subst_consts_iter_mods_def, imported_iterator_refs_ok_def, expr_ok])
    >~ [`subst_consts_areason_mods _ _`]
    >- (rename1 `subst_consts_areason_mods constants reason` >> Cases_on `reason` >>
        gvs[subst_consts_areason_mods_def, imported_assert_refs_ok_def]
        >~ [`subst_consts_error_mods _ _`] >- custom_error_case
        >> refs_simp [expr_ok])
    >~ [`subst_consts_rreason_mods _ _`]
    >- (rename1 `subst_consts_rreason_mods constants reason` >> Cases_on `reason` >>
        gvs[subst_consts_rreason_mods_def, imported_raise_refs_ok_def]
        >~ [`subst_consts_error_mods _ _`] >- custom_error_case
        >> refs_simp [expr_ok])
    >> refs_simp [subst_consts_expr_imported_refs_ok,
                  CONJUNCT1 subst_consts_target_imported_refs_ok]
  end
QED

(* Keep the statement's body variable distinct from blake2f$body. *)
val _ = hide "body";

Theorem check_contract_subst_imported_function_refs_ok:
  check_contract deploy layouts addr mods = SOME art /\
  MEM (SOME src,tls) mods /\
  MEM (FunctionDecl vis mut nr raw name args defaults ret body) tls ==>
  imported_exprs_refs_ok (subst_consts_exprs_mods (consts_env_mods mods) defaults) /\
  imported_stmts_refs_ok (subst_consts_stmts_mods (consts_env_mods mods) body)
Proof
  strip_tac >> drule_all check_contract_imported_toplevel_refs_ok >>
  simp[EVERY_MEM] >> disch_then drule >>
  simp[imported_toplevel_refs_ok_def] >> strip_tac >>
  `!key value. FST key <> NONE /\
       ALOOKUP (consts_env_mods mods) key = SOME value ==>
       imported_expr_refs_ok value` by
    (rpt strip_tac >> drule_all check_contract_const_env_imported_refs_ok >> simp[]) >>
  conj_tac
  >- (irule (CONJUNCT1 (CONJUNCT2 (CONJUNCT2 subst_consts_expr_imported_refs_ok))) >>
      simp[] >> first_assum ACCEPT_TAC)
  >> irule (CONJUNCT2 subst_consts_stmt_imported_refs_ok) >>
  simp[] >> first_assum ACCEPT_TAC
QED
