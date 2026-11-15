(* Natural byte ranges of non-reverting accesses, at occurrence boundaries. *)
Theory occurrenceAccess
Ancestors
  occurrenceGeometry ptrDiscipline o1LowerDloadOccurrence finite_map
  arithmetic codegenRel contextCodegenRel pointerConfinedDefs

(* A numeric provenance different from a protected site's erasure cannot
   contain any of its bytes.  Shared by read and write boundaries below. *)
Theorem occurrence_access_site_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\ FLOOKUP B id = SOME (b,z) /\
  FLOOKUP G v = SOME (c,w) /\ (c,w) <> (b,z) /\
  c <= off /\ off+len <= c+w /\ k < z ==>
  ~(off <= b+k /\ b+k < off+len)
Proof
  strip_tac >> Cases_on `len = 0` >- simp[] >>
  `FLOOKUP H v <> SOME id` by
    (strip_tac >> fs[occurrence_env_ok_def] >>
     first_x_assum drule >> simp[]) >>
  `0 < z /\ 0 < w` by decide_tac >>
  drule_all occurrence_env_var_site_exclusion >> decide_tac
QED

Theorem occurrence_access_write_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\ FLOOKUP B id = SOME (b,z) /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  (!ops. mem_write_ops inst = SOME ops ==>
     op_prov G ops.iao_ofst <> SOME (b,z)) /\
  MEM (off,len) (source_memory_write_ranges inst s) /\ k < z ==>
  ~(off <= b+k /\ b+k < off+len)
Proof
  strip_tac >> Cases_on `len = 0` >- simp[] >>
  `lo <= b` by metis_tac[occurrence_geometry_site_bounds] >>
  Cases_on `off+len <= lo` >- decide_tac >>
  `?ops v c w. mem_write_ops inst = SOME ops /\
      ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (c,w) /\
      c <= off /\ off+len <= c+w` by
    (fs[access_ok_def] >> metis_tac[]) >>
  `op_prov G (Var v) = SOME (c,w)` by simp[op_prov_def] >>
  `(c,w) <> (b,z)` by metis_tac[] >>
  drule_all occurrence_access_site_exclusion >> simp[]
QED

Theorem occurrence_access_read_exclusion:
  occurrence_natural_geometry lo a U B stk s /\
  occurrence_env_ok B owners H G /\ FLOOKUP B id = SOME (b,z) /\
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  (!ops. mem_read_ops inst = SOME ops ==>
     op_prov G ops.iao_ofst <> SOME (b,z)) /\
  MEM (off,len) (source_memory_read_ranges inst s) /\ k < z ==>
  ~(off <= b+k /\ b+k < off+len)
Proof
  strip_tac >> Cases_on `len = 0` >- simp[] >>
  `lo <= b` by metis_tac[occurrence_geometry_site_bounds] >>
  Cases_on `off+len <= lo` >- decide_tac >>
  `?ops v c w. mem_read_ops inst = SOME ops /\
      ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (c,w) /\
      c <= off /\ off+len <= c+w` by
    (fs[access_ok_def] >> metis_tac[]) >>
  `op_prov G (Var v) = SOME (c,w)` by simp[op_prov_def] >>
  `(c,w) <> (b,z)` by metis_tac[] >>
  drule_all occurrence_access_site_exclusion >> simp[]
QED

Theorem occurrence_access_read_slice:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  mem_read_ops inst = SOME ops /\
  op_prov G ops.iao_ofst = SOME (b,z) /\
  MEM (off,len) (source_memory_read_ranges inst s) ==>
  len = 0 \/ ?delta. off = b+delta /\ delta+len <= z
Proof
  strip_tac >> Cases_on `len = 0` >> simp[] >>
  Cases_on `ops.iao_ofst` >> gvs[op_prov_def] >>
  drule_all access_ok_read_site_bounds >> strip_tac >>
  qexists_tac `off-b` >> decide_tac
QED
