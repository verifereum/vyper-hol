Theory loadElimLatticeSoundHelpers
Ancestors
  loadElimDefs finite_map pred_set list

Definition le_lattice_holds_def:
  (le_lattice_holds P NONE <=> F) /\
  (le_lattice_holds P (SOME m) <=>
    !k vs. FLOOKUP m k = SOME vs ==> ?v. MEM v vs /\ P k v)
End

Theorem le_lattice_holds_empty[simp]:
  le_lattice_holds P (SOME FEMPTY)
Proof
  simp[le_lattice_holds_def]
QED

Theorem load_join_raw_lookup:
  FLOOKUP (load_join_raw a b) k = SOME vs ==>
  ?xs ys. FLOOKUP a k = SOME xs /\ FLOOKUP b k = SOME ys /\
    vs = operand_list_union xs ys
Proof
  simp[load_join_raw_def, FLOOKUP_FUN_FMAP] >>
  Cases_on `FLOOKUP a k` >> Cases_on `FLOOKUP b k` >>
  gvs[FLOOKUP_DEF, AllCaseEqs()]
QED

Theorem mem_operand_list_union[simp]:
  MEM v (operand_list_union xs ys) <=> MEM v xs \/ MEM v ys
Proof
  simp[operand_list_union_def, MEM_FILTER] >> metis_tac[]
QED

Theorem le_lattice_holds_join_left:
  le_lattice_holds P a ==> le_lattice_holds P (load_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[le_lattice_holds_def, load_join_def] >> rpt strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_lattice_holds_join_right:
  le_lattice_holds P b ==> le_lattice_holds P (load_join a b)
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[le_lattice_holds_def, load_join_def] >> rpt strip_tac >>
  drule load_join_raw_lookup >> strip_tac >> gvs[] >>
  metis_tac[mem_operand_list_union]
QED

Theorem le_lattice_holds_singleton:
  le_lattice_holds P ll /\
  FLOOKUP (unwrap_load_lattice ll) k = SOME [v] ==> P k v
Proof
  Cases_on `ll` >> simp[le_lattice_holds_def, unwrap_load_lattice_def] >>
  metis_tac[MEM]
QED

Theorem le_lattice_holds_every_witness:
  le_lattice_holds P ll /\
  FLOOKUP (unwrap_load_lattice ll) k = SOME vs /\ EVERY Q vs ==>
  ?v. P k v /\ Q v
Proof
  Cases_on `ll` >> simp[le_lattice_holds_def, unwrap_load_lattice_def] >>
  metis_tac[EVERY_MEM]
QED

Theorem le_lattice_holds_transport:
  le_lattice_holds P ll /\ (!k v. P k v ==> Q k v) ==>
  le_lattice_holds Q ll
Proof
  Cases_on `ll` >> simp[le_lattice_holds_def] >> metis_tac[]
QED

Theorem le_lattice_holds_restrict:
  le_lattice_holds P (SOME m) ==>
  le_lattice_holds P (SOME (DRESTRICT m keys))
Proof
  simp[le_lattice_holds_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem le_lattice_holds_update_singleton:
  le_lattice_holds P (SOME m) /\ P k v ==>
  le_lattice_holds P (SOME (m |+ (k,[v])))
Proof
  simp[le_lattice_holds_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[MEM]
QED
