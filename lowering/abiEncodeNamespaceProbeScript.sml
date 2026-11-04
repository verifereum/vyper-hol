Theory abiEncodeNamespaceProbe
Ancestors
  retAbiPlanProps compileEnv exprLowering vyperABI finite_map list

Theorem abi_encode_struct_fields_lookup:
  sfields_tenv_consistent sf tenv /\
  FLOOKUP tenv nsid = SOME (StructArgs args) ==>
  ?fields. FLOOKUP sf (nsid_to_string nsid) = SOME fields /\
    MAP FST fields = MAP FST args /\ MAP (FST o SND) fields = MAP SND args
Proof
  simp[sfields_tenv_consistent_def] >> metis_tac[]
QED

Theorem abi_encode_namespace_collision:
  nsid_to_string (SOME 0,"x") = nsid_to_string (NONE,"0.x") /\
  (SOME 0,"x") <> (NONE,"0.x")
Proof
  EVAL_TAC
QED

Theorem abi_encode_namespace_narrowing_failure:
  sfields_tenv_consistent sf tenv /\
  FLOOKUP tenv (SOME 0,"x") = SOME (StructArgs args) /\
  FLOOKUP tenv (NONE,"0.x") = SOME (StructArgs args') ==>
  ~sfields_tenv_consistent (sf \\ nsid_to_string (SOME 0,"x"))
    (tenv \\ (SOME 0,"x"))
Proof
  strip_tac >>
  simp[sfields_tenv_consistent_def, finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  disj1_tac >> qexistsl_tac [`(NONE,"0.x")`, `args'`] >>
  simp[GSYM (cj 1 abi_encode_namespace_collision)]
QED

Theorem abi_encode_namespace_narrowing_counterexample:
  sfields_tenv_consistent (FEMPTY |+ ("0.x",([] : (string # type # num) list)))
    (FEMPTY |+ ((SOME 0,"x"),StructArgs []) |+ ((NONE,"0.x"),StructArgs [])) /\
  ~sfields_tenv_consistent ((FEMPTY |+ ("0.x",([] : (string # type # num) list))) \\ nsid_to_string (SOME 0,"x"))
    ((FEMPTY |+ ((SOME 0,"x"),StructArgs []) |+ ((NONE,"0.x"),StructArgs [])) \\ (SOME 0,"x"))
Proof
  `toString (0:num) = "0"` by EVAL_TAC >>
  conj_asm1_tac
  >- (simp[sfields_tenv_consistent_def, finite_mapTheory.FLOOKUP_UPDATE,
           nsid_to_string_def] >> rpt strip_tac >>
      gvs[AllCaseEqs(), nsid_to_string_def] >>
      qexists_tac `(NONE,"0.x")` >> simp[nsid_to_string_def]) >>
  irule abi_encode_namespace_narrowing_failure >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> first_assum ACCEPT_TAC
QED
