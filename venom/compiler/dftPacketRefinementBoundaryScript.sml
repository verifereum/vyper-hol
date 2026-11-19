Theory dftPacketRefinementBoundary
Ancestors
  list rich_list option

Theorem refined_row_compatible[local]:
  !old new gs.
    LIST_REL (\old new. old = NONE \/ old = new) old new /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) new gs ==>
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) old gs
Proof
  simp[LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem list_rel_flat[local]:
  !R xss yss.
    LIST_REL (LIST_REL R) xss yss ==>
    LIST_REL R (FLAT xss) (FLAT yss)
Proof
  gen_tac >> Induct_on `xss` >> Cases_on `yss` >> simp[] >>
  rpt strip_tac >> irule EVERY2_APPEND_suff >> simp[]
QED

Theorem dft_packet_refined_flat_compatible:
  !oldrows newrows gs.
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldrows newrows /\
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT newrows) gs ==>
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) (FLAT oldrows) gs
Proof
  rpt strip_tac >> drule list_rel_flat >> strip_tac >>
  irule refined_row_compatible >> qexists_tac `FLAT newrows` >> simp[]
QED

Theorem dft_packet_refined_take_compatible:
  !oldrows newrows q kgss.
    LIST_REL (LIST_REL (\old new. old = NONE \/ old = new)) oldrows newrows /\
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE q newrows) kgss ==>
    LIST_REL (LIST_REL (\slot w. slot = NONE \/ slot = SOME w))
      (TAKE q oldrows) kgss
Proof
  Induct_on `oldrows` >> Cases_on `newrows` >> simp[] >>
  rpt gen_tac >> Cases_on `q` >> Cases_on `kgss` >> simp[] >>
  metis_tac[refined_row_compatible]
QED
