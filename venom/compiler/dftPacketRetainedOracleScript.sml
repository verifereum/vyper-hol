Theory dftPacketRetainedOracle
Ancestors
  dftPacketCommonOracle dftGasToListAgreement dftGasFromListTraceDefs sorting alist list rich_list

Theorem dft_packet_retained_key_lookup:
  ALL_DISTINCT keys /\ ALL_DISTINCT (MAP FST obs) /\
  LENGTH keys = LENGTH slots /\
  PERM (MAP (\(key,slot). (key,THE slot))
    (FILTER (\(key,slot). IS_SOME slot) (ZIP (keys,slots)))) obs ==>
  LIST_REL (\key slot. slot = ALOOKUP obs key) keys slots
Proof
  strip_tac >>
  `!key w. MEM (key,w) obs <=> MEM (key,SOME w) (ZIP (keys,slots))` by
    (rpt gen_tac >> drule PERM_MEM_EQ >>
     disch_then (qspec_then `(key,w)` mp_tac) >>
     simp[MEM_MAP, MEM_FILTER, pairTheory.EXISTS_PROD] >>
     strip_tac >> eq_tac >> rpt strip_tac
     >- (gvs[] >> Cases_on `p_2` >> gvs[]) >>
     first_x_assum (irule o iffLR) >> qexists_tac `SOME w` >> simp[]) >>
  `ALL_DISTINCT (MAP FST (ZIP (keys,slots)))` by simp[MAP_ZIP] >>
  simp[LIST_REL_EVERY_ZIP, EVERY_MEM, pairTheory.FORALL_PROD] >>
  rpt strip_tac >>
  `ALOOKUP (ZIP (keys,slots)) p_1 = SOME p_2` by
    metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  Cases_on `p_2`
  >- (Cases_on `ALOOKUP obs p_1` >> simp[] >>
      drule ALOOKUP_MEM >> strip_tac >>
      `MEM (p_1,SOME x) (ZIP (keys,slots))` by metis_tac[] >>
      metis_tac[ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11,
        optionTheory.NOT_NONE_SOME]) >>
  `MEM (p_1,x) obs` by metis_tac[] >>
  metis_tac[ALOOKUP_ALL_DISTINCT_MEM]
QED

Theorem dft_packet_retained_oracle_alignment:
  ALL_DISTINCT (MAP FST obs) /\ ALL_DISTINCT keys /\
  LIST_REL (\key slot. slot = ALOOKUP obs key) keys slots /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) slots vals /\
  EVERY (\kw. MEM kw obs) (dftGasFromListTraceDefs$trace_gas target) ==>
  let orc = (\key. case ALOOKUP (obs ++ ZIP (keys,vals)) key of
    NONE => 0w | SOME w => w) in
  agrees orc (vals ++ tail) keys /\
  dftGasFromListTraceDefs$trace_agrees orc target
Proof
  strip_tac >> simp[] >>
  `LENGTH keys = LENGTH vals` by metis_tac[LIST_REL_LENGTH] >>
  `ALL_DISTINCT (MAP FST (ZIP (keys,vals)))` by simp[MAP_ZIP] >>
  drule_all dft_packet_lookup_overlap >> strip_tac >>
  conj_tac
  >- (simp[agrees_def, padded_reading_def, EL_APPEND1] >>
      rpt strip_tac >>
      `MEM (EL i keys,EL i vals) (ZIP (keys,vals))` by
        (simp[MEM_ZIP] >> qexists_tac `i` >> simp[]) >>
      `ALOOKUP (ZIP (keys,vals)) (EL i keys) = SOME (EL i vals)` by
        metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
      qpat_x_assum `EVERY _ (ZIP _)`
        (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
      disch_then (qspec_then `(EL i keys,EL i vals)` mp_tac) >>
      simp[] >> strip_tac >> simp[ALOOKUP_APPEND]) >>
  simp[trace_agrees_def, EVERY_MEM] >>
  qx_gen_tac `kw` >> Cases_on `kw` >> simp[] >> strip_tac >>
  rename1 `(case ALOOKUP (obs ++ ZIP (keys,vals)) key of
    NONE => 0w | SOME x => x) = w` >>
  `MEM (key,w) obs` by
    (qpat_x_assum `EVERY _ (trace_gas target)`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `(key,w)` mp_tac) >> simp[]) >>
  `ALOOKUP obs key = SOME w` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM] >>
  simp[ALOOKUP_APPEND]
QED
