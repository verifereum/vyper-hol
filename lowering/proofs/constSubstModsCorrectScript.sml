(* The checker validates constants in the same order as qualified inlining. *)
Theory constSubstModsCorrect
Ancestors
  alist finite_map list option pair rich_list
  constSubst constSubstMods vyperAST vyperContext vyperCreate
  vyperInterpreter vyperTypeConstantCells vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeInitialState vyperTypeSystem vyperState

Theorem checked_ordered_const_inputs_mods:
  check_contract deploy layouts addr mods = SOME art ==>
  (?ini last. constants_fold mods ini (constants_order mods) = SOME last /\
              (!s n. declared_constant mods s n ==>
                     FLOOKUP (get_source_immutables s ini) n = NONE)) /\
  (!s ts vis e id ty slot.
     MEM (s,ts) (constants_order mods) /\
     MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
     constant_expr mods e)
Proof
  strip_tac >> conj_tac
  >- (`contract_constants_ok mods` by
        (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
         simp[check_contract_def, AllCaseEqs()]) >>
      Cases_on `initial_immutables (type_env_all_modules mods) mods` >>
      gvs[contract_constants_ok_def] >>
      rename1 `initial_immutables _ _ = SOME ini` >>
      Cases_on `constants_fold mods ini (constants_order mods)` >> gvs[] >>
      qexists_tac `ini` >> simp[declared_constant_def] >> rpt strip_tac >>
      drule_all checked_initial_immutables_constant_absent >> simp[]) >>
  simp[MEM_constants_order] >> rpt strip_tac >>
  `ALOOKUP mods s = SOME ts` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> simp[] >>
     drule check_contract_runtime_namespaces >> simp[contract_namespaces_ok_def]) >>
  drule check_contract_toplevel_decl_MEM_checked >>
  disch_then drule >> disch_then drule >> simp[check_toplevel_decl_def]
QED

Theorem consts_env_mods_acc_range:
  (!base src ts out prefix.
     constants_fold_module mods base src ts FEMPTY = SOME out /\
     (!vis e id ty slot.
        MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
        constant_expr mods e) /\
     (!s n. declared_constant mods s n /\
            IS_SOME (FLOOKUP (get_source_immutables s base) n) ==>
            IS_SOME (ALOOKUP prefix (s,n))) /\
     (!k r. ALOOKUP prefix k = SOME r ==> constant_expr [] r) ==>
     (!s n. declared_constant mods s n /\
            IS_SOME (FLOOKUP
              (get_source_immutables s (merge_constant_imms src out base)) n) ==>
            IS_SOME (ALOOKUP (module_consts_env_mods src ts prefix) (s,n))) /\
     (!k r. ALOOKUP (module_consts_env_mods src ts prefix) k = SOME r ==>
            constant_expr [] r)) ==>
  !rest base last prefix.
    constants_fold mods base rest = SOME last /\
    (!src ts vis e id ty slot.
       MEM (src,ts) rest /\ MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
       constant_expr mods e) /\
    (!s n. declared_constant mods s n /\
           IS_SOME (FLOOKUP (get_source_immutables s base) n) ==>
           IS_SOME (ALOOKUP prefix (s,n))) /\
    (!k r. ALOOKUP prefix k = SOME r ==> constant_expr [] r) ==>
    !k r. ALOOKUP (consts_env_mods_acc rest prefix) k = SOME r ==>
          constant_expr [] r
Proof
  disch_then (mk_asm "step") >> Induct
  >- (rpt gen_tac >> strip_tac >>
      rewrite_tac[consts_env_mods_acc_def] >> first_assum ACCEPT_TAC) >>
  Cases >> rename1 `(src,ts)::rest` >>
  qpat_x_assum `!b l p. _` (mk_asm "ih") >>
  map_every qx_gen_tac [`imms`,`last`,`prefix`] >> strip_tac >>
  Cases_on `constants_fold_module mods imms src ts FEMPTY` >>
  gvs[constants_fold_def, consts_env_mods_acc_def] >>
  `!vis e id ty slot.
     MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
     constant_expr mods e` by
    (qpat_assum `!u tops vis e id ty slot. _`
       (qspecl_then [`src`,`ts`] mp_tac) >> simp[]) >>
  `!u tops vis e id ty slot.
     MEM (u,tops) rest /\ MEM (VariableDecl vis (Constant e) id ty slot) tops ==>
     constant_expr mods e` by
    (map_every qx_gen_tac [`u`,`tops`] >>
     Cases_on `MEM (u,tops) rest` >> simp[] >>
     qpat_assum `!a b vis e id ty slot. _`
       (qspecl_then [`u`,`tops`] mp_tac) >> simp[]) >>
  asm "step" (drule_all_then strip_assume_tac) >>
  rename1 `constants_fold_module mods imms src ts FEMPTY = SOME out` >>
  asm "ih" (qspecl_then
    [`merge_constant_imms src out imms`, `last`,
     `module_consts_env_mods src ts prefix`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

(* Track lookup coverage and the closed range through the two module folds.
   Coverage need not identify the replacement for a shadowed name. *)
Theorem module_consts_env_mods_prefix:
  !mods base src ts m.
    (!imms prefix e.
      (!s n. declared_constant mods s n /\
             IS_SOME (FLOOKUP (get_source_immutables s imms) n) ==>
             ?r. ALOOKUP prefix (s,n) = SOME r /\ constant_expr [] r) /\
      constant_expr mods e /\ IS_SOME (constant_value mods imms e) ==>
      constant_expr [] (fold_const_expr (subst_consts_expr_mods prefix e))) ==>
    !out prefix.
      constants_fold_module mods base src ts m = SOME out /\
      (!vis e id ty slot. MEM (VariableDecl vis (Constant e) id ty slot) ts ==>
         constant_expr mods e) /\
      (!s n. declared_constant mods s n /\
             IS_SOME (FLOOKUP (get_source_immutables s (merge_constant_imms src m base)) n) ==>
             IS_SOME (ALOOKUP prefix (s,n))) /\
      (!k r. ALOOKUP prefix k = SOME r ==> constant_expr [] r) ==>
      (!s n. declared_constant mods s n /\
             IS_SOME (FLOOKUP (get_source_immutables s (merge_constant_imms src out base)) n) ==>
             IS_SOME (ALOOKUP (module_consts_env_mods src ts prefix) (s,n))) /\
      (!k r. ALOOKUP (module_consts_env_mods src ts prefix) k = SOME r ==>
             constant_expr [] r)
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rpt conj_tac >>
  pure_rewrite_tac[constants_fold_module_def, module_consts_env_mods_def]
  >- (simp[] >> rpt strip_tac >> first_x_assum irule >> goal_assum ACCEPT_TAC)
  >- (rpt (gen_tac ORELSE disch_tac) >>
      pop_assum strip_assume_tac >>
      qpat_x_assum `(case _ of NONE => _ | SOME _ => _) = SOME _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [AllCaseEqs()]) >>
      qpat_x_assum `!vis e id ty slot. MEM _ (_::_) ==> _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [DISJ_IMP_THM, FORALL_AND_THM]) >>
      qmatch_assum_rename_tac
        `constant_value ms (merge_constant_imms sid acc ini) init = SOME value` >>
      rename1 `evaluate_type (type_env_all_modules ms) _ = SOME tv` >>
      qpat_x_assum `!tv value. evaluate_type _ _ = SOME tv /\ constant_value _ _ _ = SOME value ==> _`
        (qspecl_then [`tv`, `value`] mp_tac) >>
      (impl_tac >- simp[]) >> (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then match_mp_tac >> simp[] >>
      (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
      >- (map_every qx_gen_tac [`query_src`, `query_id`] >> strip_tac >>
          qpat_assum `!s n. _ ==> IS_SOME (ALOOKUP prefix (s,n))`
            (qspecl_then [`query_src`, `query_id`] mp_tac) >>
          Cases_on `ALOOKUP prefix (query_src,query_id)` >> simp[ALOOKUP_APPEND] >>
          Cases_on `query_src = sid` >> Cases_on `query_id = id` >>
          gvs[merge_constant_imms_def, FLOOKUP_FUNION,
              get_source_immutables_set_same, get_source_immutables_set_other,
              FLOOKUP_UPDATE, IS_SOME_EQ_NOT_NONE]) >>
      `constant_expr [] (fold_const_expr (subst_consts_expr_mods prefix init))` by
        (qpat_assum `!imms prefix e. _ ==> constant_expr [] _`
           (qspec_then `merge_constant_imms sid acc ini` match_mp_tac) >>
         simp[] >> map_every qx_gen_tac [`s`, `n`] >> strip_tac >>
         qpat_assum `!s n. _ ==> IS_SOME (ALOOKUP prefix (s,n))`
           (drule_all_then mp_tac) >>
         Cases_on `ALOOKUP prefix (s,n)` >> simp[] >>
         metis_tac[]) >>
      rpt gen_tac >> Cases_on `ALOOKUP prefix k` >>
      rw[ALOOKUP_APPEND] >> gvs[] >> metis_tac[]) >>
  rpt (gen_tac ORELSE disch_tac) >> pop_assum strip_assume_tac >>
  qpat_x_assum `!vis e id ty slot. MEM _ (_::_) ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  last_x_assum mp_tac >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then match_mp_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem successful_initializer_closed_mods:
  (!src id. declared_constant mods src id /\
      IS_SOME (FLOOKUP (get_source_immutables src imms) id) ==>
      ?rhs. ALOOKUP env (src,id) = SOME rhs /\ constant_expr [] rhs) /\
  constant_expr mods e /\ IS_SOME (constant_value mods imms e) ==>
  constant_expr [] (fold_const_expr (subst_consts_expr_mods env e))
Proof
  rpt strip_tac >>
  `(!x. constant_expr [] x ==> constant_expr [] (fold_const_expr x)) /\
   (!t:base_assignment_target. T) /\
   (!es. EVERY (constant_expr []) es ==>
         EVERY (constant_expr []) (fold_const_exprs es)) /\
   (!d:expr option. T) /\
   (!fs. EVERY (constant_expr []) (MAP SND fs) ==>
         EVERY (constant_expr []) (MAP SND (fold_const_fields fs)))` by
    (ho_match_mp_tac fold_const_expr_ind >>
     simp[constant_expr_def, fold_const_expr_def, SF ETA_ss] >>
     rpt strip_tac >>
     `EVERY (constant_expr []) (fold_const_exprs es)` by simp[] >>
     qmatch_goalsub_abbrev_tac `fold_const_builtin ty bi args` >>
     Cases_on `bi` >> gvs[fold_const_builtin_def, constant_expr_def, SF ETA_ss] >>
     Cases_on `args` >> gvs[constant_expr_def, SF ETA_ss] >>
     rename1 `_ :: rest` >> Cases_on `rest` >> gvs[constant_expr_def, SF ETA_ss] >>
     rename1 `[arg]` >> Cases_on `arg` >> gvs[constant_expr_def, SF ETA_ss] >>
     rename1 `Literal aty lit` >> Cases_on `lit` >>
     gvs[constant_expr_def, SF ETA_ss]) >>
  `(!x. constant_expr mods x /\ IS_SOME (constant_value mods imms x) ==>
        constant_expr [] (subst_consts_expr_mods env x)) /\
   (!t:base_assignment_target. T) /\
   (!es. EVERY (constant_expr mods) es /\ IS_SOME (constant_values mods imms es) ==>
         EVERY (constant_expr []) (subst_consts_exprs_mods env es)) /\
   (!d:expr option. T) /\
   (!fs. EVERY (constant_expr mods) (MAP SND fs) /\
         IS_SOME (constant_values mods imms (MAP SND fs)) ==>
         EVERY (constant_expr []) (MAP SND (subst_consts_fields_mods env fs)))`
     suffices_by simp[] >>
  qpat_x_assum `constant_expr mods e` kall_tac >>
  qpat_x_assum `IS_SOME (constant_value mods imms e)` kall_tac >>
  ho_match_mp_tac fold_const_expr_ind >>
  simp[constant_expr_def, subst_consts_expr_mods_def, constant_value_def, SF ETA_ss] >>
  rpt conj_tac >> rpt (gen_tac ORELSE (disch_then strip_assume_tac)) >>
  gvs[IS_SOME_MAP]
  >- (PairCases_on `ns` >>
      gvs[constant_expr_def, subst_consts_expr_mods_def, constant_value_def] >>
      Cases_on `ALOOKUP mods ns0` >> gvs[] >>
      rename1 `ALOOKUP mods ns0 = SOME tops` >>
      Cases_on `IS_SOME (find_var_decl_by_name ns1 tops)` >> gvs[IS_SOME_MAP] >>
      qpat_x_assum `!src id. declared_constant _ _ _ /\ _ ==> _` drule >>
      simp[] >> strip_tac >> simp[])
  >- (Cases_on `constant_value mods imms x` >> gvs[] >>
      Cases_on `constant_value mods imms x'` >> gvs[])
  >- (Cases_on `constant_value mods imms x` >> gvs[])
  >- (Cases_on `constant_values mods imms es` >> gvs[])
  >- (Cases_on `constant_values mods imms es` >> gvs[])
  >- (Cases_on `constant_value mods imms x` >> gvs[] >>
      Cases_on `constant_values mods imms es` >> gvs[]) >>
  Cases_on `constant_value mods imms x` >> gvs[] >>
  Cases_on `constant_values mods imms (MAP SND fs)` >> gvs[]
QED

Theorem constant_expr_empty_subst_mods:
  (!e. constant_expr [] e ==> subst_consts_expr_mods env e = e) /\
  (!es. EVERY (constant_expr []) es ==> subst_consts_exprs_mods env es = es) /\
  (!fs. EVERY (constant_expr []) (MAP SND fs) ==>
        subst_consts_fields_mods env fs = fs)
Proof
  `(!e. constant_expr [] e ==> subst_consts_expr_mods env e = e) /\
   (!t:base_assignment_target. T) /\
   (!es. EVERY (constant_expr []) es ==> subst_consts_exprs_mods env es = es) /\
   (!d:expr option. T) /\
   (!fs. EVERY (constant_expr []) (MAP SND fs) ==>
         subst_consts_fields_mods env fs = fs)` suffices_by simp[] >>
  ho_match_mp_tac fold_const_expr_ind >>
  simp[constant_expr_def, subst_consts_expr_mods_def, SF ETA_ss] >>
  rpt gen_tac >> PairCases_on `ns` >>
  simp[constant_expr_def, declared_constant_def]
QED

(* At each prefix, every declared constant key present in the checker's
   immutables has a replacement in the compiler's prefix environment.
   Initial immutables contain no such keys. Successful evaluation of a
   constant initializer therefore resolves all of its top-level names in
   the prefix environment. Folding the substituted expression cannot add
   any names. *)
Theorem checked_consts_env_mods_closed:
  check_contract deploy layouts addr mods = SOME art ==>
  !id rhs. ALOOKUP (consts_env_mods mods) id = SOME rhs ==>
           !env. subst_consts_expr_mods env rhs = rhs
Proof
  strip_tac >> drule_then strip_assume_tac checked_ordered_const_inputs_mods >>
  rename1 `constants_fold mods ini (constants_order mods) = SOME last` >>
  rpt gen_tac >> simp[consts_env_mods_def, consts_env_modules_order_eq] >> strip_tac >>
  `constant_expr [] rhs` by
    (mp_tac consts_env_mods_acc_range >>
     (impl_tac >-
       (map_every qx_gen_tac [`imms0`, `src`, `ts`, `out`, `prefix`] >> strip_tac >>
        qspecl_then [`mods`, `imms0`, `src`, `ts`, `FEMPTY`] mp_tac
          module_consts_env_mods_prefix >>
        (impl_tac >- (rpt strip_tac >> drule_all successful_initializer_closed_mods >> simp[])) >>
        disch_then (qspecl_then [`out`, `prefix`] mp_tac) >>
        (impl_tac >-
          (`!s. get_source_immutables s (merge_constant_imms src FEMPTY imms0) =
                get_source_immutables s imms0` by
             (gen_tac >> Cases_on `s = src` >>
              simp[merge_constant_imms_def, get_source_immutables_set_same,
                   get_source_immutables_set_other]) >>
           simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC)) >>
     disch_then (qspecl_then [`constants_order mods`, `ini`, `last`, `[]`] mp_tac) >>
     (impl_tac >-
       (simp[] >> (conj_tac >- first_assum ACCEPT_TAC) >>
        rpt gen_tac >> Cases_on `declared_constant mods s n` >> simp[] >>
        qpat_assum `!s n. _ ==> FLOOKUP _ n = NONE` (drule_then ACCEPT_TAC))) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  simp[constant_expr_empty_subst_mods]
QED

Triviality subst_consts_expr_mods_idempotent:
  (!id rhs. ALOOKUP env id = SOME rhs ==> subst_consts_expr_mods env rhs = rhs) ==>
  (!e. subst_consts_expr_mods env (subst_consts_expr_mods env e) =
       subst_consts_expr_mods env e) /\
  (!t. subst_consts_btarget_mods env (subst_consts_btarget_mods env t) =
       subst_consts_btarget_mods env t) /\
  (!es. subst_consts_exprs_mods env (subst_consts_exprs_mods env es) =
        subst_consts_exprs_mods env es) /\
  (!d. subst_consts_opt_mods env (subst_consts_opt_mods env d) =
       subst_consts_opt_mods env d) /\
  (!fs. subst_consts_fields_mods env (subst_consts_fields_mods env fs) =
        subst_consts_fields_mods env fs)
Proof
  strip_tac >> ho_match_mp_tac fold_const_expr_ind >>
  simp[subst_consts_expr_mods_def] >>
  rpt gen_tac >> PairCases_on `ns` >>
  Cases_on `ALOOKUP env (ns0,ns1)` >>
  simp[subst_consts_expr_mods_def] >>
  first_x_assum drule >> simp[]
QED

Theorem const_subst_blueprint_literal_offset_mods:
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  check_contract deploy layouts addr mods = SOME art ==>
  blueprint_literal_offset cx has_salt
    (subst_consts_exprs_mods (consts_env_mods mods) es) =
  blueprint_literal_offset cx has_salt es
Proof
  strip_tac >>
  `!xs. subst_consts_exprs_mods (consts_env_mods mods) xs =
        MAP (subst_consts_expr_mods (consts_env_mods mods)) xs` by
    (Induct >> simp[subst_consts_expr_mods_def]) >>
  `!id rhs. ALOOKUP (consts_env_mods mods) id = SOME rhs ==>
            subst_consts_expr_mods (consts_env_mods mods) rhs = rhs` by
    (rpt gen_tac >> strip_tac >>
     drule checked_consts_env_mods_closed >>
     disch_then (drule_then (qspec_then `consts_env_mods mods` ACCEPT_TAC))) >>
  drule subst_consts_expr_mods_idempotent >> strip_tac >>
  simp[blueprint_literal_offset_def, GSYM MAP_DROP] >>
  Cases_on `DROP (if has_salt then 3 else 2) es` >> simp[]
QED
