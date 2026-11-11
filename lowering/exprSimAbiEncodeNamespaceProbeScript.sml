(* Diagnostic sufficient condition, not an expression precondition. *)
Theory exprSimAbiEncodeNamespaceProbe
Ancestors
  loweringStateRelDefs
    compileEnv finite_map words

Theorem abi_encode_namespace_collision:
  nsid_to_string (NONE,"0.S") = nsid_to_string (SOME 0,"S") /\
  (NONE,"0.S") <> (SOME 0,"S")
Proof
  EVAL_TAC
QED

Theorem abi_encode_sfields_delete_separated:
  sfields_tenv_consistent sf tenv /\
  (!k a. FLOOKUP tenv k = SOME (StructArgs a) /\ k <> nsid ==>
    nsid_to_string k <> nsid_to_string nsid) ==>
  sfields_tenv_consistent (sf \\ nsid_to_string nsid) (tenv \\ nsid)
Proof
  strip_tac >>
  fs[sfields_tenv_consistent_def, DOMSUB_FLOOKUP_THM] >> rpt strip_tac
  >~ [`nsid_to_string _ <> name`]
  >- (res_tac >> qexistsl_tac [`nsid'`, `args`] >> simp[] >>
      strip_tac >> gvs[])
QED
