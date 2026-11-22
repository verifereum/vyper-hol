(* Replay a checked module fold using the declared cells of its final slot. *)
Theory vyperLinkedConstantSlotReplay
Ancestors
  vyperAST vyperInterpreter vyperState vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeConstantCells vyperTypeConstantFold
  vyperLinkedConstantFoldTrace vyperConstantFoldReplay
  alist finite_map list option sorting

Theorem checked_ordered_fold_slot_replay:
  check_contract T layouts addr mods = SOME art /\
  initial_immutables (type_env_all_modules mods) mods = SOME init /\
  constants_fold mods init (constants_order mods) = SOME last /\
  (!sid nm. declared_constant mods sid nm ==>
     FLOOKUP (get_source_immutables sid dst) nm =
     FLOOKUP (get_source_immutables sid last) nm) ==>
  !src tops. MEM (src,tops) mods ==>
    ?cenv. constants_fold_module mods dst src tops FEMPTY = SOME cenv /\
           cenv SUBMAP get_source_immutables src dst
Proof
  rpt strip_tac >>
  `contract_namespaces_ok F mods` by
    metis_tac[check_contract_runtime_namespaces] >>
  `ALL_DISTINCT (MAP FST mods)` by fs[contract_namespaces_ok_def] >>
  `ALL_DISTINCT (MAP FST (constants_order mods))` by
    metis_tac[ALL_DISTINCT_PERM, PERM_MAP, PERM_constants_order] >>
  `EVERY (\m. MEM m mods) (constants_order mods)` by
    simp[EVERY_MEM, MEM_constants_order] >>
  `!s ts id. MEM (s,ts) (constants_order mods) /\
             declared_constant mods s id ==>
     FLOOKUP (get_source_immutables s init) id = NONE` by
    (simp[declared_constant_def] >> rpt strip_tac >>
     drule_all checked_initial_immutables_constant_absent >> simp[]) >>
  `MEM (src,tops) (constants_order mods)` by simp[MEM_constants_order] >>
  drule_all constants_fold_member_trace >>
  disch_then (qx_choose_then `ref` (qx_choose_then `env` strip_assume_tac)) >>
  qexists `env` >> conj_tac
  >- (irule constants_fold_module_replay_present >> conj_tac
      >- (`ALOOKUP mods src = SOME tops` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
          rpt strip_tac >> drule check_contract_toplevel_decl_MEM_checked >>
          disch_then drule >> disch_then drule >> simp[check_toplevel_decl_def]) >>
      qexists `ref` >> simp[] >> rpt strip_tac >>
      gvs[IS_SOME_EXISTS] >> metis_tac[SUBMAP_FLOOKUP_EQN]) >>
  simp[SUBMAP_FLOOKUP_EQN] >> rpt strip_tac >>
  `x IN FDOM env` by metis_tac[flookup_thm] >>
  metis_tac[SUBMAP_FLOOKUP_EQN]
QED
