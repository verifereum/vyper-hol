Theory loadElimNonempty
Ancestors
  loadElimDefs loadElimTransferProvenance loadElimLatticeSoundHelpers
  loadElimConvergence loadElimSolverHelpers loadElimSupportHelpers
  loadElimOrderHelpers dfAnalyzeProofs dfAnalyzeDefs
  finite_map list pred_set

Definition le_lists_nonempty_def:
  le_lists_nonempty ll <=>
    !k vs. FLOOKUP (unwrap_load_lattice ll) k = SOME vs ==> vs <> []
End

Theorem le_lists_nonempty_initial[simp]:
  le_lists_nonempty NONE /\ le_lists_nonempty (SOME FEMPTY)
Proof
  simp[le_lists_nonempty_def, unwrap_load_lattice_def]
QED

Theorem le_lists_nonempty_transfer:
  le_lists_nonempty ll ==> le_lists_nonempty (load_transfer ctx inst ll)
Proof
  simp[le_lists_nonempty_def] >> rpt strip_tac >>
  drule le_transfer_lookup_origin >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem le_lists_nonempty_join:
  le_lists_nonempty a /\ le_lists_nonempty b ==>
  le_lists_nonempty (load_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >> simp[load_join_def] >>
  simp[le_lists_nonempty_def, unwrap_load_lattice_def] >> rpt strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  fs[operand_list_union_def] >> metis_tac[]
QED
