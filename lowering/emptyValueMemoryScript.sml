Theory emptyValueMemory
Ancestors
  valueEncoding valueEncodingProofs valueEncodingProps vyperTyping

Theorem empty_layout_memory[local]:
  (!tv. type_memory_size tv = 0 ==>
    !v p mem. val_wf tv v ==> val_in_memory tv v p mem) /\
  (!tvs. type_memory_size_list tvs = 0 ==>
    !vs p mem. tuple_val_wf vs tvs ==> tuple_in_memory vs tvs p mem) /\
  (!fts. type_memory_size_fields fts = 0 ==>
    !vs p mem. fields_val_wf vs fts ==> fields_in_memory vs fts p mem)
Proof
  ho_match_mp_tac type_memory_size_ind >>
  simp[type_memory_size_def] >>
  rpt strip_tac >>
  all_tac
  >~ [`val_in_memory NoneTV v p mem`]
  >- (Cases_on `v` >> gvs[val_wf_def, val_in_memory_def, type_memory_size_def,
                         AllCaseEqs()] >> Cases_on `a` >> gvs[val_wf_def])
  >~ [`tuple_in_memory vs [] p mem`]
  >- (Cases_on `vs` >> gvs[val_wf_def, val_in_memory_def])
  >~ [`fields_in_memory vs [] p mem`]
  >- (Cases_on `vs` >- simp[val_in_memory_def] >>
      Cases_on `h` >> gvs[val_wf_def, val_in_memory_def])
  >~ [`tuple_in_memory vs (tv::tvs) p mem`]
  >- (Cases_on `vs` >> gvs[val_wf_def, val_in_memory_def] >> metis_tac[])
  >~ [`fields_in_memory vs ((name,tv)::fts) p mem`]
  >- (Cases_on `vs` >> simp[val_in_memory_def] >> Cases_on `h` >>
      gvs[val_wf_def, val_in_memory_def] >> metis_tac[])
  >~ [`val_in_memory (TupleTV tvs) v p mem`]
  >- (Cases_on `v` >> gvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
      Cases_on `a` >> gvs[val_wf_def, val_in_memory_def] >> metis_tac[])
  >~ [`val_in_memory (StructTV fts) v p mem`]
  >- (Cases_on `v` >> gvs[val_wf_def, val_in_memory_def, type_memory_size_def] 
      >~ [`val_in_memory (StructTV fts) (ArrayV a) p mem`]
      >- (Cases_on `a` >> gvs[val_wf_def, val_in_memory_def]) >> metis_tac[])
  >> Cases_on `v` >>
  gvs[val_wf_def, val_in_memory_def, type_memory_size_def] >>
  Cases_on `a` >> gvs[val_wf_def, val_in_memory_def] >>
  all_tac
  >~ [`kvs_val_wf l tv 0`]
  >- (Cases_on `l` >> simp[val_in_memory_def] >> Cases_on `h` >>
      gvs[val_wf_def]) >>
  reverse conj_tac
  >- metis_tac[val_wf_default_value_proof] >>
  qpat_x_assum `kvs_val_wf _ _ _` mp_tac >>
  Induct_on `l` >> simp[val_wf_def, val_in_memory_def] >>
  Cases_on `h` >> simp[val_wf_def, val_in_memory_def] >> metis_tac[]
QED

Theorem zero_layout_val_in_memory:
  value_has_type tv v /\ val_wf tv v /\ type_memory_size tv = 0 ==>
  val_in_memory tv v p mem
Proof
  metis_tac[empty_layout_memory]
QED
