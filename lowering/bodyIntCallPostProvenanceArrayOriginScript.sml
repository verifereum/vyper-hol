(* Source-origin probes: conditionals materialize storage values rather than
   returning their places. These facts do not infer source origin from bytes. *)
Theory bodyIntCallPostProvenanceArrayOrigin
Ancestors vyperInterpreter vyperState pair

Theorem conditional_result_nonstorage:
  conditional_result cx raw es = (INL tv,ee) ==>
  !tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)
Proof
  Cases_on `raw`
  >~ [`Value v`] >- (simp[conditional_result_def, return_def] >> rpt strip_tac >> gvs[]) 
  >~ [`HashMapRef tr slot kt vt`] >- simp[conditional_result_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  simp[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> simp[bind_def, return_def, AllCaseEqs()]
QED

Theorem select_result_nonstorage_origin:
  select_result cx ty raw sb es = (INL out,ee) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  (!tr slot kt vt. raw <> HashMapRef tr slot kt vt) ==>
  (!tr slot vt. out <> PlaceR (StoragePlace tr slot vt)) /\
  (!tr slot kt vt. out <> HashMapRef tr slot kt vt)
Proof
  Cases_on `raw`
  >~ [`HashMapRef tr slot kt vt`] >- metis_tac[]
  >~ [`Value v`] >-
    (simp[select_result_def, bind_def, return_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[]) >>
  rename1 `PlaceR p` >> Cases_on `p`
  >~ [`StoragePlace tr slot vt`] >- metis_tac[] >>
  simp[select_result_def, extend_place_def, extend_memory_place_def,
       bind_def, ignore_bind_def, return_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED
