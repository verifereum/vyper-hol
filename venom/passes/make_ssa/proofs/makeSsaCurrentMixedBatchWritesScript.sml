Theory makeSsaCurrentMixedBatchWrites
Ancestors makeSsaCurrentBatchWrites makeSsaCurrentPhiBatch
  makeSsaCurrentValueInvariant venomState finite_map alist list rich_list

Theorem current_reverse_updates_lookup:
  !pairs m. FLOOKUP (FOLDL (\m dv. m |+ dv) m (REVERSE pairs)) v =
    case ALOOKUP pairs v of NONE => FLOOKUP m v | SOME value => SOME value
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[REVERSE_DEF, FOLDL_APPEND, FLOOKUP_UPDATE] >>
  Cases_on `h0 = v` >> simp[]
QED

Theorem current_singleton_agree_mixed_reverse_pairs:
  current_singleton_agree table st st' /\
  (!v n. MEM (v,n) table ==> ALOOKUP pairs v = ALOOKUP pairs' n) ==>
  current_singleton_agree table
    (st with vs_vars := FOLDL (\m dv. m |+ dv) st.vs_vars (REVERSE pairs))
    (st' with vs_vars := FOLDL (\m dv. m |+ dv) st'.vs_vars (REVERSE pairs'))
Proof
  simp[current_singleton_agree_def, lookup_var_def, current_reverse_updates_lookup] >>
  rpt strip_tac >>
  first_x_assum drule >> disch_then SUBST1_TAC >>
  Cases_on `ALOOKUP pairs' n` >> simp[] >> metis_tac[]
QED

Theorem current_singleton_agree_mixed_phi_batches:
  current_singleton_agree table before before' /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  EVERY (\inst. inst.inst_opcode = PHI) phis' /\
  LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs /\
  LIST_REL (\inst dv. eval_one_phi before' inst = SOME dv) phis' pairs' /\
  (!v n. MEM (v,n) table ==> ALOOKUP pairs v = ALOOKUP pairs' n) ==>
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
  drule_all current_singleton_agree_mixed_reverse_pairs >>
  simp[current_singleton_agree_def, lookup_var_def]
QED

Theorem current_alookup_distinct_correspondence:
  ALL_DISTINCT (MAP FST pairs) /\ ALL_DISTINCT (MAP FST pairs') /\
  (!value. MEM (v,value) pairs <=> MEM (n,value) pairs') ==>
  ALOOKUP pairs v = ALOOKUP pairs' n
Proof
  strip_tac >>
  Cases_on `ALOOKUP pairs v` >> Cases_on `ALOOKUP pairs' n` >> simp[] >>
  metis_tac[ALOOKUP_MEM, ALOOKUP_ALL_DISTINCT_MEM, optionTheory.option_CLAUSES]
QED

Theorem current_singleton_agree_mixed_phi_batches_distinct:
  current_singleton_agree table before before' /\
  EVERY (\inst. inst.inst_opcode = PHI) phis /\
  EVERY (\inst. inst.inst_opcode = PHI) phis' /\
  LIST_REL (\inst dv. eval_one_phi before inst = SOME dv) phis pairs /\
  LIST_REL (\inst dv. eval_one_phi before' inst = SOME dv) phis' pairs' /\
  ALL_DISTINCT (MAP FST pairs) /\ ALL_DISTINCT (MAP FST pairs') /\
  (!v n value. MEM (v,n) table ==> (MEM (v,value) pairs <=> MEM (n,value) pairs')) ==>
  ?after after'. eval_phis before phis = OK after /\
    eval_phis before' phis' = OK after' /\
    current_singleton_agree table after after'
Proof
  rpt strip_tac >> irule current_singleton_agree_mixed_phi_batches >>
  asm_rewrite_tac[] >> qexistsl_tac [`pairs`, `pairs'`] >> simp[] >>
  rpt strip_tac >> irule current_alookup_distinct_correspondence >>
  metis_tac[]
QED
