Theory bodyLookupLiteralCasesMods
Ancestors
  bodyFullPredsMods bodyNameLookupPathsMods bodyQualifiedLookupPlaceMods
  bodyWordLiteralMods bodyAllocLiteralMods compileEnv vyperAST

Theorem body_name_case_full_mods:
  !mods exps cx ann id. body_expr_full_ok_mods mods exps cx (Name ann id)
Proof
  simp[name_lookup_full_ok_mods]
QED

Theorem body_toplevel_name_case_full_mods:
  !mods exps cx ann nsid.
    body_expr_full_ok_mods mods exps cx (TopLevelName ann nsid)
Proof
  irule qualified_name_lookup_full_ok_mods >>
  rpt gen_tac >> disch_tac >>
  match_mp_tac qualified_lookup_place_mods >> first_assum ACCEPT_TAC
QED

Theorem body_literal_case_full_mods:
  !mods exps cx ann l. body_expr_full_ok_mods mods exps cx (Literal ann l)
Proof
  rpt gen_tac >> Cases_on `is_word_type ann` >>
  simp[word_literal_full_ok_mods, alloc_literal_full_ok_mods]
QED
