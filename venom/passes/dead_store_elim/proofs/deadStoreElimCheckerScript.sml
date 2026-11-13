(* Soundness of the executable dead-store check: dse_checked_analysis meets
   all_dead_stores for any candidate list. *)
Theory deadStoreElimChecker
Ancestors
  deadStoreElimCheckerDefs deadStoreElimDefs cfgDefs list rich_list
  relation arithmetic

Theorem dse_read_before_clobber_EL:
  !l. dse_read_before_clobber aliases bp space loc l <=>
      ?j. j < LENGTH l /\
          (!k. k < j ==> ~dse_inst_clobbers bp space loc (EL k l)) /\
          dse_inst_reads_alias aliases bp space loc (EL j l)
Proof
  Induct >> simp[dse_read_before_clobber_def] >> rpt strip_tac >> eq_tac
  >- (strip_tac
      >- (qexists_tac `0` >> simp[]) >>
      qexists_tac `SUC j` >> simp[] >>
      Cases >> simp[]) >>
  strip_tac >> Cases_on `j` >- fs[] >>
  disj2_tac >> conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qexists_tac `n` >> fs[] >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]
QED

Theorem dse_clobber_free_eq:
  dse_clobber_free bp space loc fn lbl <=>
  block_no_full_clobber bp space loc fn lbl
Proof
  simp[dse_clobber_free_def, block_no_full_clobber_def, EVERY_MEM] >>
  metis_tac[]
QED

Theorem dse_rest_read_before_clobber[local]:
  j > inst_idx /\ j < LENGTH l /\
  (!k. inst_idx < k /\ k < j ==> ~dse_inst_clobbers bp space loc (EL k l)) /\
  dse_inst_reads_alias aliases bp space loc (EL j l) ==>
  dse_read_before_clobber aliases bp space loc (DROP (SUC inst_idx) l)
Proof
  rw[dse_read_before_clobber_EL] >>
  qexists_tac `j - SUC inst_idx` >> simp[EL_DROP] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `k + SUC inst_idx` mp_tac) >> simp[EL_DROP]
QED

Theorem dse_rest_clobber[local]:
  EXISTS (dse_inst_clobbers bp space loc) (DROP (SUC inst_idx) l) ==>
  ?k. inst_idx < k /\ k < LENGTH l /\ dse_inst_clobbers bp space loc (EL k l)
Proof
  rw[EXISTS_MEM, MEM_EL] >>
  qexists_tac `n + SUC inst_idx` >> gvs[EL_DROP]
QED

Theorem dse_unclobbered_read_exists[local]:
  block_has_unclobbered_read aliases bp space loc fn lbl ==>
  EXISTS (\bb'. bb'.bb_label = lbl /\
                dse_read_before_clobber aliases bp space loc bb'.bb_instructions)
         fn.fn_blocks
Proof
  rw[block_has_unclobbered_read_def, EXISTS_MEM, dse_read_before_clobber_EL] >>
  metis_tac[]
QED

Theorem dse_reach_mem[local]:
  !n lbls. MEM x lbls ==>
    MEM x (FUNPOW (dse_reach_step cfg bp space loc fn) n lbls)
Proof
  Induct >> simp[FUNPOW_SUC, dse_reach_step_def]
QED

Theorem dse_reach_closed[local]:
  !a b. RTC (\a b. MEM b (cfg_succs_of cfg a) /\
                   block_no_full_clobber bp space loc fn a) a b ==>
        (!lbl. MEM lbl reached /\ block_no_full_clobber bp space loc fn lbl ==>
               !l. MEM l (cfg_succs_of cfg lbl) ==> MEM l reached) /\
        MEM a reached ==> MEM b reached
Proof
  ho_match_mp_tac RTC_INDUCT >> simp[] >> metis_tac[]
QED

Theorem dse_not_live_check_sound:
  dse_not_live_check cfg aliases bp loc space fn bb inst_idx ==>
  ~dse_mem_def_live cfg aliases bp loc space fn bb inst_idx
Proof
  rewrite_tac[dse_not_live_check_def] >> simp_tac std_ss [LET_THM] >>
  qabbrev_tac `reached = FUNPOW (dse_reach_step cfg bp space loc fn)
                           (SUC (LENGTH fn.fn_blocks))
                           (cfg_succs_of cfg bb.bb_label)` >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  rewrite_tac[dse_mem_def_live_def] >> strip_tac
  >- metis_tac[dse_rest_read_before_clobber] >>
  qpat_x_assum `EXISTS _ _ \/ EVERY _ _` strip_assume_tac
  >- metis_tac[dse_rest_clobber] >>
  qpat_x_assum `EVERY _ reached`
    (strip_assume_tac o SIMP_RULE std_ss [EVERY_MEM, dse_clobber_free_eq]) >>
  `MEM succ_lbl reached` by
    (simp[Abbr `reached`] >> irule dse_reach_mem >> simp[]) >>
  `!lbl. MEM lbl reached /\ block_no_full_clobber bp space loc fn lbl ==>
         !l. MEM l (cfg_succs_of cfg lbl) ==> MEM l reached` by metis_tac[] >>
  `MEM target_lbl reached` by (drule dse_reach_closed >> metis_tac[]) >>
  metis_tac[dse_unclobbered_read_exists]
QED

Theorem dse_checked_analysis_dead_stores:
  all_dead_stores (dse_checked_analysis cand space fn) (cfg_analyze fn)
    FEMPTY (bp_analyze (cfg_analyze fn) fn) space fn
Proof
  rewrite_tac[all_dead_stores_def] >> rpt strip_tac >>
  `dse_dead_store_check (cfg_analyze fn) FEMPTY
     (bp_analyze (cfg_analyze fn) fn) space fn id` by
    fs[dse_checked_analysis_def, MEM_FILTER] >>
  pop_assum mp_tac >>
  simp_tac std_ss [dse_dead_store_check_def, EXISTS_MEM, MEM_COUNT_LIST,
                   LET_THM] >>
  strip_tac >>
  qexistsl_tac [`bb`, `inst_idx`] >>
  simp[outputs_unused_def] >>
  irule dse_not_live_check_sound >> simp[]
QED
