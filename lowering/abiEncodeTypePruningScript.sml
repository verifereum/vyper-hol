Theory abiEncodeTypePruning
Ancestors
  retAbiPlanProps vyperTyping compileEnv vyperValue finite_map list

Theorem abi_encode_struct_alias_value:
  sfields_tenv_consistent sf tenv /\ nsid_to_string a = nsid_to_string b /\
  evaluate_type tenv (StructT a) = SOME va /\
  evaluate_type tenv (StructT b) = SOME vb ==> va = vb
Proof
  strip_tac >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[Once evaluate_type_def, AllCaseEqs()] >>
  `MAP FST args = MAP FST args' /\ MAP SND args = MAP SND args'` by
    (gvs[sfields_tenv_consistent_def] >>
     qpat_assum `!nsid args. FLOOKUP tenv nsid = SOME (StructArgs args) ==> _`
       (qspecl_then [`a`, `args`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
     qpat_x_assum `!nsid args. FLOOKUP tenv nsid = SOME (StructArgs args) ==> _`
       (qspecl_then [`b`, `args'`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then strip_assume_tac >> gvs[]) >>
  `tenv \\ a SUBMAP tenv /\ tenv \\ b SUBMAP tenv` by
    simp[SUBMAP_FLOOKUP_EQN, DOMSUB_FLOOKUP_THM] >>
  `evaluate_types tenv (MAP SND args) [] = SOME tvs` by
    metis_tac[cj 2 vyper_to_abi_type_submap] >>
  `evaluate_types tenv (MAP SND args') [] = SOME tvs'` by
    metis_tac[cj 2 vyper_to_abi_type_submap] >>
  gvs[]
QED
