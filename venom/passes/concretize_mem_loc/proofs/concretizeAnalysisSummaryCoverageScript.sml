Theory concretizeAnalysisSummaryCoverage
Ancestors
  concretizeMemLocDefs list pair

(* Deduplication preserves keys, not triples with inconsistent metadata. *)
Theorem unique_mems_used_key_mem:
  !xs. MEM a (MAP FST (unique_mems_used xs)) <=> MEM a (MAP FST xs)
Proof
  recInduct unique_mems_used_ind >> simp[unique_mems_used_def] >>
  rpt strip_tac >> simp[MEM_MAP, MEM_FILTER] >>
  Cases_on `a = a'` >> gvs[] >>
  simp[pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem unique_mems_used_key_coverage:
  MEM (a,p,sz) xs ==> ?p' sz'. MEM (a,p',sz') (unique_mems_used xs)
Proof
  strip_tac >>
  `MEM a (MAP FST xs)` by (simp[MEM_MAP] >> metis_tac[FST]) >>
  `MEM a (MAP FST (unique_mems_used xs))` by
    simp[unique_mems_used_key_mem] >>
  gvs[MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]
QED
