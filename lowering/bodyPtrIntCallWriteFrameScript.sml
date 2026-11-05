(* Ordinary write exclusion; exceptional revert forwarding is explicit. *)
Theory bodyPtrIntCallWriteFrame
Ancestors bodyPtrIntCallConfinement ptrDiscipline pred_set arithmetic

Theorem intcall_access_write_outside:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  intcall_prov_outside P PG G /\ (!i. i < lo ==> i NOTIN P) /\
  MEM (off,len) (source_memory_write_ranges inst s) /\
  off <= a /\ a < off + len ==> a NOTIN P
Proof
  rpt strip_tac >>
  Cases_on `lo < off + len`
  >- (fs[access_ok_def] >>
      `len <> 0` by decide_tac >>
      qpat_x_assum `!off len. MEM (off,len) (source_memory_write_ranges inst s) /\ _ ==> _` drule >>
      simp[] >> rpt strip_tac >>
      fs[intcall_prov_outside_def] >>
      qpat_x_assum `!x site. FLOOKUP G x = SOME site ==> _` drule >>
      simp[intcall_site_outside_def, DISJOINT_DEF, EXTENSION] >>
      disch_then (qspec_then `a` mp_tac) >> simp[] >> decide_tac) >>
  `a < lo` by decide_tac >> metis_tac[]
QED
