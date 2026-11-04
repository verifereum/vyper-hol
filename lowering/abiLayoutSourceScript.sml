(* Source-only successful type evaluation transport, below compiler layout. *)
Theory abiLayoutSource
Ancestors
  vyperValue vyperABI finite_map list pair

Theorem vyper_to_abi_type_submap:
  (!env ty tv.
     evaluate_type env ty = SOME tv ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_type tenv ty = SOME tv /\
            vyper_to_abi_type env ty = vyper_to_abi_type tenv ty) /\
  (!env ts acc tvs.
     evaluate_types env ts acc = SOME tvs ==>
     !tenv. env SUBMAP tenv ==>
            evaluate_types tenv ts acc = SOME tvs /\
            vyper_to_abi_types env ts = vyper_to_abi_types tenv ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >>
      gvs[evaluate_type_def, AllCaseEqs()] >>
      `FLOOKUP tenv nsid = SOME (StructArgs args)`
        by fs[SUBMAP_FLOOKUP_EQN] >>
      `env \\ nsid SUBMAP tenv \\ nsid`
        by fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      first_x_assum drule >> simp[])
  >~ [`FlagT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      fs[SUBMAP_FLOOKUP_EQN])
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule >> Cases_on `bd` >> simp[])
  >> rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem vyper_abi_layout_submap:
  (!env ty tv. evaluate_type env ty = SOME tv ==>
    !root. env SUBMAP root ==>
      vyper_is_dynamic env ty = vyper_is_dynamic root ty /\
      vyper_abi_size_bound env ty = vyper_abi_size_bound root ty) /\
  (!env ts acc tvs. evaluate_types env ts acc = SOME tvs ==>
    !root. env SUBMAP root ==>
      vyper_any_dynamic env ts = vyper_any_dynamic root ts /\
      vyper_abi_size_bound_list env ts = vyper_abi_size_bound_list root ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac
  >~ [`StructT nsid`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      `FLOOKUP root nsid = SOME (StructArgs args)`
        by fs[SUBMAP_FLOOKUP_EQN] >>
      `env \\ nsid SUBMAP root \\ nsid`
        by fs[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
      first_x_assum drule >>
      simp[vyper_is_dynamic_def, vyper_abi_size_bound_def])
  >~ [`FlagT nsid`]
  >- simp[vyper_is_dynamic_def, vyper_abi_size_bound_def]
  >~ [`ArrayT t bd`]
  >- (rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
      first_x_assum drule >> Cases_on `bd` >>
      simp[vyper_is_dynamic_def, vyper_abi_size_bound_def])
  >> rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()] >>
  simp[vyper_is_dynamic_def, vyper_abi_size_bound_def] >>
  metis_tac[]
QED
