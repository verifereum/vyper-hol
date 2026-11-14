Theory dftGasPacketRefinement
Ancestors
  list rich_list sorting arithmetic option

(* A successful actual GAS promotes only its own padded occurrence row.
   The caller supplies the dynamic row mapping and the real nonempty pop. *)
Theorem occurrence_packet_gas_refinement:
  LIST_REL (\m es. LENGTH m = LENGTH es) ms ess /\
  j < LENGTH ms /\ EL j ms = [NONE] /\
  PERM (MAP THE (FILTER IS_SOME (FLAT ms)) ++ w::unused) initial_readings /\
  ms' = LUPDATE [SOME w] j ms ==>
  LENGTH ms' = LENGTH ess /\
  LIST_REL (\m es. LENGTH m = LENGTH es) ms' ess /\
  PERM (MAP THE (FILTER IS_SOME (FLAT ms')) ++ unused) initial_readings /\
  (!q. q < LENGTH ms /\ q <> j ==> EL q ms' = EL q ms) /\
  (!gss. LIST_REL
      (LIST_REL (\slot x. slot = NONE \/ slot = SOME x)) ms' gss ==>
    LIST_REL (LIST_REL (\slot x. slot = NONE \/ slot = SOME x)) ms gss /\
    EL j gss = [w])
Proof
  strip_tac >>
  `LENGTH ms = LENGTH ess` by metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (EL j ess) = 1` by
    (fs[LIST_REL_EL_EQN] >>
     first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
  `LIST_REL (\m es. LENGTH m = LENGTH es) ms' ess` by
    (fs[LIST_REL_EL_EQN] >> rpt strip_tac >>
     simp[EL_LUPDATE] >> Cases_on `n = j` >> gvs[] >> metis_tac[]) >>
  `?pre post. ms = pre ++ [NONE]::post /\ LENGTH pre = j` by
    (qexistsl_tac [`TAKE j ms`, `DROP (SUC j) ms`] >>
     conj_tac
     >- (drule rich_listTheory.TAKE_DROP_SUC >>
         qpat_assum `EL j ms = [NONE]` (fn row =>
           simp_tac pure_ss [row, APPEND, GSYM APPEND_ASSOC]) >>
         POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
     simp[LENGTH_TAKE]) >>
  `ms' = pre ++ [SOME w]::post` by
    (qpat_assum `LENGTH pre = j` (fn idx =>
     qpat_assum `ms = pre ++ [NONE]::post` (fn packets =>
     qpat_assum `ms' = LUPDATE [SOME w] j ms` (fn update =>
       ACCEPT_TAC (REWRITE_RULE [packets, GSYM idx, LUPDATE_LENGTH] update))))) >>
  `PERM (MAP THE (FILTER IS_SOME (FLAT ms')) ++ unused)
        (MAP THE (FILTER IS_SOME (FLAT ms)) ++ w::unused)` by
    (qpat_assum `ms = pre ++ [NONE]::post` (fn packets =>
       pure_rewrite_tac[packets]) >>
     qpat_assum `ms' = pre ++ [SOME w]::post` (fn promoted =>
       pure_rewrite_tac[promoted]) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac list_ss [FILTER_APPEND, MAP_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND, PERM_APPEND_IFF] >>
     metis_tac[CONS_PERM, PERM_REFL]) >>
  conj_tac >- metis_tac[LIST_REL_LENGTH] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[PERM_TRANS] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `ms' = LUPDATE [SOME w] j ms` (fn update =>
      qpat_assum `q <> j` (fn other =>
        simp[NoAsms, update, other, EL_LUPDATE]))) >>
  gen_tac >> strip_tac >>
  `j < LENGTH ms'` by metis_tac[LIST_REL_LENGTH] >>
  `EL j ms' = [SOME w]` by
    (qpat_assum `ms' = LUPDATE [SOME w] j ms` (fn update =>
     qpat_assum `j < LENGTH ms` (fn bound =>
       simp[NoAsms, update, bound, EL_LUPDATE]))) >>
  `LIST_REL (\slot x. slot = NONE \/ slot = SOME x) [SOME w] (EL j gss)` by
    (qpat_assum `LIST_REL _ ms' gss` (fn relation =>
       assume_tac (CONJUNCT2 (ONCE_REWRITE_RULE [LIST_REL_EL_EQN] relation))) >>
     first_x_assum (qspec_then `j` mp_tac) >>
     qpat_assum `j < LENGTH ms'` (fn bound =>
     qpat_assum `EL j ms' = [SOME w]` (fn row =>
       simp_tac std_ss [bound, row]))) >>
  `EL j gss = [w]` by
    (qpat_assum `LIST_REL _ [SOME w] (EL j gss)` (fn relation =>
       ACCEPT_TAC (SIMP_RULE (srw_ss()) [LIST_REL_CONS1] relation))) >>
  `LUPDATE [NONE] j ms' = ms` by
    (qpat_assum `ms = pre ++ [NONE]::post` (fn packets =>
     qpat_assum `ms' = pre ++ [SOME w]::post` (fn promoted =>
     qpat_assum `LENGTH pre = j` (fn idx =>
       simp_tac std_ss [packets, promoted, GSYM idx, LUPDATE_LENGTH])))) >>
  `j < LENGTH gss` by metis_tac[LIST_REL_LENGTH] >>
  `LUPDATE [w] j gss = gss` by
    (drule LUPDATE_SAME >>
     qpat_assum `EL j gss = [w]` (fn row => simp_tac std_ss [row])) >>
  `LIST_REL (\slot x. slot = NONE \/ slot = SOME x) [NONE] [w]` by simp[] >>
  conj_tac >- metis_tac[LIST_REL_LUPDATE_same] >> first_assum ACCEPT_TAC
QED
