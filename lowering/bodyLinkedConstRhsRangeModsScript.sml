(* Checked linked constant environments have syntactically closed RHSs. *)
Theory bodyLinkedConstRhsRangeMods
Ancestors vyperTypeEnv[qualified,ignore_grammar] vyperTypeInitialState[qualified,ignore_grammar] vyperConstantFoldReplay[qualified,ignore_grammar] vyperInterpreter[qualified,ignore_grammar] vyperContext[qualified,ignore_grammar] vyperState[qualified,ignore_grammar] finite_map[qualified,ignore_grammar]
  constSubstModsCorrect constSubstCorrect constSubstMods vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeConstantCells

Theorem checked_const_rhs_constant_expr_mods:
  check_contract mode layouts addr mods = SOME art ==>
  !key rhs. ALOOKUP (consts_env_mods mods) key = SOME rhs ==>
            constant_expr [] rhs
Proof
  strip_tac >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def]) >>
  `?ini last. constants_fold mods ini (constants_order mods) = SOME last /\
              (!s n. declared_constant mods s n ==>
                     FLOOKUP (get_source_immutables s ini) n = NONE)` by
    (qpat_x_assum `contract_constants_ok mods` mp_tac >>
     Cases_on `initial_immutables (type_env_all_modules mods) mods` >>
     gvs[contract_constants_ok_def, optionTheory.IS_SOME_EXISTS] >>
     strip_tac >>
     qexistsl [`x`, `x'`] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `declared_constant mods s n` mp_tac >>
     simp[declared_constant_def] >>
     strip_tac >>
     drule_all checked_initial_immutables_constant_absent >>
     simp[]) >>
  rename1 `constants_fold mods ini (constants_order mods) = SOME last` >>
  rpt gen_tac >> simp[constSubstModsTheory.consts_env_mods_def,
      vyperInterpreterTheory.consts_env_modules_order_eq] >> strip_tac >>
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
              simp[merge_constant_imms_def,
                   vyperTypeInitialStateTheory.get_source_immutables_set_same,
                   vyperTypeInitialStateTheory.get_source_immutables_set_other]) >>
           simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC)) >>
     disch_then (qspecl_then [`constants_order mods`, `ini`, `last`, `[]`] mp_tac) >>
     (impl_tac >-
       (simp[] >> conj_tac
        >- (simp[vyperInterpreterTheory.MEM_constants_order] >>
            rpt gen_tac >> strip_tac >>
            `ALL_DISTINCT (MAP FST mods)` by
              (drule check_contract_runtime_namespaces >>
               simp[contract_namespaces_ok_def]) >>
            drule_all_then assume_tac alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
            drule_all checked_const_decl_typed >> simp[])
        >- (rpt gen_tac >>
            `declared_constant mods s n ==>
               FLOOKUP (get_source_immutables s ini) n = NONE` by
              (strip_tac >>
               qpat_x_assum `declared_constant mods s n` mp_tac >>
               simp[declared_constant_def] >>
               strip_tac >>
               drule_all checked_initial_immutables_constant_absent >>
               simp[]) >>
            metis_tac[]))) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  simp[constant_expr_empty_subst_mods]
QED
