Theory requestCutPacketFillings
Ancestors dftPacketFillingBoundary list rich_list

Theorem request_cut_packet_level_fillings:
  !cs (prev:'cut -> 'slot list list) active (R:'slot -> 'word -> bool) gs.
    LIST_REL R (FLAT (MAP (\c. FLAT (prev c) ++ FLAT (active c)) cs)) gs ==>
    ?gcs. gs = FLAT gcs /\ LENGTH gcs = LENGTH cs /\
      !i. i < LENGTH cs ==>
        ?gps gas. EL i gcs = FLAT gps ++ FLAT gas /\
          LIST_REL (LIST_REL R) (prev (EL i cs)) gps /\
          LIST_REL (LIST_REL R) (active (EL i cs)) gas
Proof
  rpt gen_tac >> strip_tac >>
  drule dft_packet_flat_filling_split >> strip_tac >>
  qexists_tac `gss` >> simp[] >>
  conj_tac >- metis_tac[LIST_REL_LENGTH,LENGTH_MAP] >>
  gen_tac >> strip_tac >>
  `LIST_REL R (FLAT (prev (EL i cs)) ++ FLAT (active (EL i cs))) (EL i gss)` by
    (qpat_assum `LIST_REL (LIST_REL R) (MAP _ cs) gss`
      (fn th => qspec_then `i` mp_tac (CONJUNCT2 (REWRITE_RULE [LIST_REL_EL_EQN] th))) >>
     simp[EL_MAP,LIST_REL_EL_EQN]) >>
  qpat_assum `LIST_REL R (FLAT (prev _) ++ FLAT (active _)) _`
    (strip_assume_tac o REWRITE_RULE [LIST_REL_SPLIT1]) >>
  qpat_assum `LIST_REL R (FLAT (prev _)) ys1`
    (fn th => strip_assume_tac (MATCH_MP (SPEC_ALL dft_packet_flat_filling_split) th)) >>
  qpat_assum `LIST_REL R (FLAT (active _)) ys2`
    (fn th => strip_assume_tac (MATCH_MP (SPEC_ALL dft_packet_flat_filling_split) th)) >>
  qexistsl_tac [`gss'`,`gss''`] >> simp[]
QED
