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

Theorem dft_key_map_flat_length:
  !rows keyrows.
    LIST_REL (\ss kk. LENGTH ss = LENGTH kk) rows keyrows ==>
    LENGTH (FLAT rows) = LENGTH (FLAT keyrows)
Proof
  Induct_on `rows` >> Cases_on `keyrows` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem dft_packet_flat_length:
  !ord. (!e. MEM e ord ==> LENGTH (keys e) = LENGTH (masks e)) ==>
    LENGTH (FLAT (MAP keys ord)) = LENGTH (FLAT (MAP masks ord))
Proof
  Induct >> simp[]
QED

Theorem dft_packet_flat_pair:
  !ord. (!e. MEM e ord ==> LENGTH (keys e) = LENGTH (masks e)) /\
    MEM e ord /\ MEM kv (ZIP (keys e,masks e)) ==>
    MEM kv (ZIP (FLAT (MAP keys ord),FLAT (MAP masks ord)))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `LENGTH (keys h) = LENGTH (masks h)` by metis_tac[] >>
  `LENGTH (FLAT (MAP keys ord)) = LENGTH (FLAT (MAP masks ord))` by
    (irule dft_packet_flat_length >> metis_tac[]) >>
  simp[GSYM ZIP_APPEND] >> metis_tac[]
QED

Theorem dft_packet_row_pair:
  !rows keyrows q.
    LIST_REL (\m k. LENGTH m = LENGTH k) rows keyrows /\
    q < LENGTH rows /\ MEM kv (ZIP (EL q keyrows,EL q rows)) ==>
    MEM kv (ZIP (FLAT keyrows,FLAT rows))
Proof
  Induct >> Cases_on `keyrows` >> simp[] >> rpt gen_tac >> strip_tac >>
  drule dft_key_map_flat_length >> disch_tac >>
  simp[GSYM ZIP_APPEND] >> Cases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem dft_packet_unflat_lookup:
  !R rows keys.
    LIST_REL (\r k. LENGTH r = LENGTH k) rows keys /\
    LIST_REL R (FLAT keys) (FLAT rows) ==>
    LIST_REL (LIST_REL R) keys rows
Proof
  gen_tac >> Induct >> Cases_on `keys` >> simp[] >>
  rpt strip_tac >> gvs[LIST_REL_APPEND_EQ]
QED

Theorem dft_packet_flat_prefix_lookup:
  !R ks ms. LIST_REL (LIST_REL R) ks ms ==>
    !q. LIST_REL R (FLAT (TAKE q ks)) (FLAT (TAKE q ms))
Proof
  gen_tac >> Induct >> Cases_on `ms` >> simp[] >>
  rpt gen_tac >> strip_tac >> gen_tac >> Cases_on `q` >> simp[] >>
  irule LIST_REL_APPEND_suff >> simp[]
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
