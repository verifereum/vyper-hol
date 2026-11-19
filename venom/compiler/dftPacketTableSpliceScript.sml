Theory dftPacketTableSplice
Ancestors
  list rich_list finite_map

Theorem dft_packet_row_prefix_splice:
  !k q v rows. k <= q ==> TAKE k (LUPDATE v q rows) = TAKE k rows
Proof
  Induct_on `rows` >- simp[LUPDATE_def] >>
  rpt gen_tac >> Cases_on `k` >- simp[] >>
  Cases_on `q` >> simp[LUPDATE_def]
QED

Theorem dft_packet_activation_splice_frame:
  !a b e newrows tab tab' order.
    b <> a /\ tab' = tab |+ ((a,e),newrows) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab' (b,f)))) order) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (b,f)))) order)
Proof
  simp[FLOOKUP_UPDATE_DIFF]
QED

Theorem dft_packet_activation_row_splice:
  !a e ds later order rows q (v:'v list) tab tab'.
    order = ds ++ e::later /\ ALL_DISTINCT order /\
    FLOOKUP tab (a,e) = SOME rows /\ q < LENGTH rows /\
    tab' = tab |+ ((a,e), LUPDATE v q rows) ==>
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab' (a,f)))) order) =
    FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds) ++
      FLAT (TAKE q rows) ++ v ++ FLAT (DROP (SUC q) rows) ++
      FLAT (MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) later)
Proof
  rpt strip_tac >> gvs[ALL_DISTINCT_APPEND] >>
  `LUPDATE v q rows = TAKE q rows ++ [v] ++ DROP (SUC q) rows` by
    (qsuff_tac `!(rs:'v list list) n x. n < LENGTH rs ==>
       LUPDATE x n rs = TAKE n rs ++ [x] ++ DROP (SUC n) rs`
     >- metis_tac[] >>
     Induct >- simp[] >> rpt gen_tac >>
     Cases_on `n` >> simp[LUPDATE_def]) >>
  `MAP (\f. FLAT (THE (FLOOKUP (tab |+ ((a,e),LUPDATE v q rows)) (a,f)))) ds =
   MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) ds` by
    (irule MAP_CONG >> simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  `MAP (\f. FLAT (THE (FLOOKUP (tab |+ ((a,e),LUPDATE v q rows)) (a,f)))) later =
   MAP (\f. FLAT (THE (FLOOKUP tab (a,f)))) later` by
    (irule MAP_CONG >> simp[FLOOKUP_UPDATE] >> metis_tac[]) >>
  simp[MAP_APPEND, FLAT_APPEND, FLOOKUP_UPDATE, APPEND_ASSOC]
QED
