Theory makeSsaCurrentBatchWrites
Ancestors makeSsaCurrentValueInvariant makeSsaCurrentSemanticHistory
  venomExecSemantics venomState finite_map list rich_list pair

Theorem current_eval_phis_from_witness:
  !phis pairs. EVERY (\inst. inst.inst_opcode = PHI) phis /\
    LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs ==>
  ?after. eval_phis before phis = OK after /\
    after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars (REVERSE pairs)
Proof
  Induct >- simp[eval_phis_def] >>
  Cases_on `pairs` >> simp[] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  PairCases_on `h` >>
  simp[eval_phis_def, REVERSE_DEF, FOLDL_APPEND, update_var_def]
QED

Theorem current_singleton_agree_reverse_pairs:
  !pairs pairs' st st'.
    LIST_REL (\dv dv'. SND dv = SND dv' /\
      current_table_write_aligned table (FST dv) (FST dv')) pairs pairs' /\
    current_singleton_agree table st st' ==>
    current_singleton_agree table
      (st with vs_vars := FOLDL (\m dv. m |+ dv) st.vs_vars (REVERSE pairs))
      (st' with vs_vars := FOLDL (\m dv. m |+ dv) st'.vs_vars (REVERSE pairs'))
Proof
  Induct >- simp[] >> Cases_on `pairs'` >> simp[] >>
  rpt strip_tac >> first_x_assum drule_all >>
  PairCases_on `h` >> PairCases_on `h'` >>
  simp[REVERSE_DEF, FOLDL_APPEND] >> strip_tac >> gvs[] >>
  drule_all current_singleton_agree_write >>
  simp[update_var_def]
QED

Theorem current_singleton_agree_phi_batches:
  current_singleton_agree table before before' /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  EVERY (\inst. inst.inst_opcode = PHI) phis' /\
  LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs /\
  LIST_REL (\inst dv. eval_one_phi before' inst = SOME dv) phis' pairs' /\
  LIST_REL (\dv dv'. SND dv = SND dv' /\
    current_table_write_aligned table (FST dv) (FST dv')) pairs pairs' ==>
  ?after after'. eval_phis before phis = OK after /\
    eval_phis before' phis' = OK after' /\
    current_singleton_agree table after after'
Proof
  rpt strip_tac >>
  `?after. eval_phis before phis = OK after /\
    after.vs_vars = FOLDL (\m dv. m |+ dv) before.vs_vars (REVERSE pairs)` by
    metis_tac[current_eval_phis_from_witness] >>
  `?after'. eval_phis before' phis' = OK after' /\
    after'.vs_vars = FOLDL (\m dv. m |+ dv) before'.vs_vars (REVERSE pairs')` by
    metis_tac[current_eval_phis_from_witness] >>
  qexistsl_tac [`after`, `after'`] >> simp[] >>
  drule_all current_singleton_agree_reverse_pairs >>
  simp[current_singleton_agree_def, lookup_var_def]
QED
