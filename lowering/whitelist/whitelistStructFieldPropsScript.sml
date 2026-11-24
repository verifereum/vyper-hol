Theory whitelistStructFieldProps
Ancestors
  alist list pair option

Theorem structlit_fields_lookup:
  MAP FST fields = MAP FST declared ==>
  EVERY (\(name,e). IS_SOME (ALOOKUP declared name)) fields
Proof
  rw[EVERY_MEM, FORALL_PROD] >>
  `MEM p_1 (MAP FST fields)` by (simp[MEM_MAP, EXISTS_PROD] >> metis_tac[]) >>
  Cases_on `ALOOKUP declared p_1` >> gvs[ALOOKUP_NONE]
QED
