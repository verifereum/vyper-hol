Theory dftPacketBlockCutAggregate
Ancestors
  list rich_list pair

Theorem dft_packet_block_cut_aggregate:
  !(tab : ('path # num) -> 'slot list list) tab' A
    (priorcuts : ('path # num list # num # num # 'z) list)
    p ds d q z0 z1 oldcuts newcuts.
  (!U cuts. A U cuts =
    FLAT (MAP (\(ai,ds,ei,qi,zi).
      FLAT (MAP (\f. FLAT (U (ai,f))) ds) ++
      FLAT (TAKE qi (U (ai,ei)))) cuts)) /\
  oldcuts = priorcuts ++ [(p,ds,d,0,z0)] /\
  newcuts = priorcuts ++ [(p,ds ++ [d],SUC d,q,z1)] /\
  (!ai ds ei qi zi. MEM (ai,ds,ei,qi,zi) priorcuts ==>
    FLAT (MAP (\f. FLAT (tab' (ai,f))) ds) ++
      FLAT (TAKE qi (tab' (ai,ei))) =
    FLAT (MAP (\f. FLAT (tab (ai,f))) ds) ++
      FLAT (TAKE qi (tab (ai,ei)))) /\
  (!f. MEM f ds ==> tab' (p,f) = tab (p,f)) ==>
  A tab' newcuts = A tab oldcuts ++ FLAT (tab' (p,d)) ++
    FLAT (TAKE q (tab' (p,SUC d))) /\
  MAP (\(ai,ds,ei,qi,zi). ai) newcuts =
    MAP (\(ai,ds,ei,qi,zi). ai) oldcuts
Proof
  rpt gen_tac >> strip_tac >>
  `MAP (\(ai,ds,ei,qi,zi).
     FLAT (MAP (\f. FLAT (tab' (ai,f))) ds) ++
       FLAT (TAKE qi (tab' (ai,ei)))) priorcuts =
   MAP (\(ai,ds,ei,qi,zi).
     FLAT (MAP (\f. FLAT (tab (ai,f))) ds) ++
       FLAT (TAKE qi (tab (ai,ei)))) priorcuts` by
    (irule listTheory.MAP_CONG >> simp[] >>
     rpt gen_tac >> strip_tac >> PairCases_on `x` >>
     simp[] >> metis_tac[]) >>
  `MAP (\f. FLAT (tab' (p,f))) ds =
   MAP (\f. FLAT (tab (p,f))) ds` by
    (irule listTheory.MAP_CONG >> simp[]) >>
  gvs[] >> simp[MAP_APPEND,FLAT_APPEND,APPEND_ASSOC]
QED

Theorem dft_packet_block_filling_split:
  !R (M0 : 'slot list) Mb M1 (gs : 'value list).
  LIST_REL R (M0 ++ Mb ++ M1) gs ==>
  ?g0 gb g1.
    gs = g0 ++ gb ++ g1 /\
    LIST_REL R M0 g0 /\ LIST_REL R Mb gb /\ LIST_REL R M1 g1 /\
    LENGTH g0 = LENGTH M0 /\ LENGTH gb = LENGTH Mb /\
    LENGTH g1 = LENGTH M1
Proof
  rpt gen_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,LIST_REL_SPLIT1] >>
  strip_tac >> gvs[APPEND_ASSOC] >>
  metis_tac[LIST_REL_LENGTH]
QED
