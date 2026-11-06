Theory o1MakeSsaCallOwnership
Ancestors
  o1MakeSsaOwnership o1MakeSsaFlags makeSsaCurrentDefs list pred_set

Theorem current_rename_owner_outputs:
  !outs s rs rs' s' ns V H.
  rename_current_outputs s rs outs = (rs',s',ns) /\
  current_rename_owner V H s rs /\ set outs SUBSET V ==>
  ?H'. H SUBSET H' /\ current_rename_owner V H' s' rs'
Proof
  Induct >- (simp[rename_current_outputs_def] >> metis_tac[SUBSET_REFL]) >>
  rpt gen_tac >> simp[rename_current_outputs_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[INSERT_SUBSET] >>
  drule_all current_rename_owner_push >> strip_tac >>
  first_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `H''` >> simp[] >> metis_tac[SUBSET_TRANS]
QED

Theorem current_rename_owner_inst:
  rename_current_inst s rs inst = (rs',s',inst') /\
  current_rename_owner V H s rs /\ set inst.inst_outputs SUBSET V ==>
  ?H'. H SUBSET H' /\ current_rename_owner V H' s' rs'
Proof
  simp[rename_current_inst_def] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule_all current_rename_owner_outputs >> simp[]
QED

Theorem current_rename_owner_block_insts:
  !insts s rs rs' s' insts' V H.
  rename_current_block_insts s rs insts = (rs',s',insts') /\
  current_rename_owner V H s rs /\
  EVERY (\i. set i.inst_outputs SUBSET V) insts ==>
  ?H'. H SUBSET H' /\ current_rename_owner V H' s' rs'
Proof
  Induct >- (simp[rename_current_block_insts_def] >> metis_tac[SUBSET_REFL]) >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all current_rename_owner_inst >> strip_tac >>
  first_x_assum drule >> disch_then drule >> simp[] >> strip_tac >>
  qexists_tac `H''` >> simp[] >> metis_tac[SUBSET_TRANS]
QED

Theorem current_flag_alias_outputs_copy:
  !outs s rs rs' s' ns V H vs ws.
  rename_current_outputs s rs outs = (rs',s',ns) /\
  current_rename_owner V H s rs /\ set outs SUBSET V /\
  current_flag_alias rs vs ws ==>
  current_flag_alias rs' (outs ++ vs) (ns ++ ws)
Proof
  Induct >- simp[rename_current_outputs_def] >>
  rpt gen_tac >> simp[rename_current_outputs_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[INSERT_SUBSET] >>
  drule_all current_rename_owner_push >> strip_tac >>
  drule_all current_flag_alias_copy >> strip_tac >>
  first_x_assum drule >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`h::vs`,`name::ws`] mp_tac) >>
  simp[] >> simp[current_flag_alias_def, MEM_APPEND] >> metis_tac[]
QED

Theorem current_flag_alias_outputs_kill:
  !outs s rs rs' s' ns V H vs ws.
  rename_current_outputs s rs outs = (rs',s',ns) /\
  current_rename_owner V H s rs /\ set outs SUBSET V /\
  set vs SUBSET V /\ current_flag_alias rs vs ws ==>
  current_flag_alias rs' (FILTER (\v. ~MEM v outs) vs)
                         (FILTER (\n. ~MEM n ns) ws)
Proof
  Induct >- simp[rename_current_outputs_def] >>
  rpt gen_tac >> simp[rename_current_outputs_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[INSERT_SUBSET] >>
  `!w. MEM w vs /\ w <> h ==> latest_current_name rs w <> name` by
    (rpt gen_tac >> strip_tac >> irule current_rename_owner_nonclobber >>
     gvs[SUBSET_DEF] >> metis_tac[]) >>
  drule_all current_flag_alias_redefine >> strip_tac >>
  drule_all current_rename_owner_push >> strip_tac >>
  first_x_assum drule >> disch_then drule >> simp[] >>
  disch_then (qspecl_then [`FILTER (\w. w <> h) vs`,
                          `FILTER (\w. w <> name) ws`] mp_tac) >>
  simp[] >>
  `set (FILTER (\w. w <> h) vs) SUBSET V` by
    gvs[SUBSET_DEF, MEM_FILTER] >>
  simp[] >> simp[current_flag_alias_def, MEM_FILTER] >> metis_tac[]
QED
