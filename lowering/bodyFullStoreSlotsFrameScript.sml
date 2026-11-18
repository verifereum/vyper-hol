Theory bodyFullStoreSlotsFrame
Ancestors
  stmtSimStoreCopy ptrDiscipline venomState list

(* Normalization forgets control and variables, not the allocation frame. *)
Theorem store_slots_normalize_allocas_below_fmp:
  store_copy_normalize s t = u ==>
  (allocas_below_fmp t <=> allocas_below_fmp u)
Proof
  strip_tac >>
  qpat_x_assum `store_copy_normalize s t = u`
    (mp_tac o AP_TERM ``allocas_below_fmp``) >>
  simp[store_copy_normalize_def, allocas_below_fmp_def]
QED

(* Storage updates leave every field read by the FMP invariant unchanged. *)
Theorem store_slots_fold_allocas_below_fmp:
  allocas_below_fmp
    (FOLDL (\q j. (if tr then tstore else sstore) (key j) (value j) q)
      s (ks:num list)) <=> allocas_below_fmp s
Proof
  qid_spec_tac `s` >> Induct_on `ks` >- simp[] >>
  gen_tac >> simp[FOLDL] >>
  Cases_on `tr` >> simp[sstore_def, tstore_def, allocas_below_fmp_def]
QED
