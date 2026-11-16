Theory dftPacketKeyMap
Ancestors
  list rich_list finite_map

Theorem dft_key_map_flat:
  !rows keyrows H.
    LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keyrows ==>
    FLAT (MAP2 (\ss kk. MAP2 H ss kk) rows keyrows) =
      MAP2 H (FLAT rows) (FLAT keyrows)
Proof
  Induct_on `rows` >> Cases_on `keyrows` >>
  simp[MAP2, MAP2_APPEND]
QED

Theorem dft_key_map_lookup:
  !H M Ktab M'.
    M' = FMAP_MAP2 (\(ae,rows).
      MAP2 (\ss kk. MAP2 H ss kk) rows (THE (FLOOKUP Ktab ae))) M ==>
    FDOM M' = FDOM M /\
    (!ae rows keyrows.
      FLOOKUP M ae = SOME rows /\ FLOOKUP Ktab ae = SOME keyrows ==>
      FLOOKUP M' ae = SOME (MAP2 (\ss kk. MAP2 H ss kk) rows keyrows))
Proof
  rpt strip_tac >> gvs[FMAP_MAP2_THM, FLOOKUP_FMAP_MAP2]
QED

Theorem dft_key_map_flat_length[local]:
  !rows keyrows.
    LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keyrows ==>
    LENGTH (FLAT rows) = LENGTH (FLAT keyrows)
Proof
  Induct_on `rows` >> Cases_on `keyrows` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem dft_key_map_order_flat:
  !H M Ktab M' a order.
    M' = FMAP_MAP2 (\(ae,rows).
      MAP2 (\ss kk. MAP2 H ss kk) rows (THE (FLOOKUP Ktab ae))) M ==>
    (!e. MEM e order ==>
      ?rows keyrows.
        FLOOKUP M (a,e) = SOME rows /\
        FLOOKUP Ktab (a,e) = SOME keyrows /\
        LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keyrows) ==>
    FLAT (MAP (\e. FLAT (THE (FLOOKUP M' (a,e)))) order) =
    MAP2 H
      (FLAT (MAP (\e. FLAT (THE (FLOOKUP M (a,e)))) order))
      (FLAT (MAP (\e. FLAT (THE (FLOOKUP Ktab (a,e)))) order))
Proof
  rpt gen_tac >> disch_tac >> gvs[] >>
  Induct_on `order` >- simp[] >>
  rpt strip_tac >>
  qpat_assum `!e. _` (qspec_then `h` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  simp[FLOOKUP_FMAP_MAP2, dft_key_map_flat,
       MAP2_APPEND, dft_key_map_flat_length] >>
  first_x_assum irule >> metis_tac[]
QED
