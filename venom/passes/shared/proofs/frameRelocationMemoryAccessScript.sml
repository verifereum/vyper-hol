Theory frameRelocationMemoryAccess
Ancestors ptrDiscipline venomExecSemantics finite_map

(* Classify both read and write ranges before choosing target geometry.
   An unresolved offset lies in the static prefix or at or above the
   dynamic floor dyn (the frame's vs_initial_fmp). *)
Theorem resolved_memory_access:
  access_ok lo G fn inst s /\ ~in_revert_forward fn s /\
  (!v e. FLOOKUP rv v = SOME e ==> FLOOKUP G v = SOME (SND e)) /\
  (!v site. FLOOKUP G v = SOME site /\ FLOOKUP rv v = NONE ==>
     dyn <= FST site) /\ len <> 0 /\
  ((MEM (off,len) (source_memory_write_ranges inst s) /\
    mem_write_ops inst = SOME ops) \/
   (MEM (off,len) (source_memory_read_ranges inst s) /\
    mem_read_ops inst = SOME ops)) ==>
  (((off + len <= lo \/ dyn <= off) /\
    (!v. ops.iao_ofst = Var v ==> FLOOKUP rv v = NONE)) \/
   (?v token b sz. ops.iao_ofst = Var v /\
     FLOOKUP rv v = SOME (token,(b,sz)) /\
     b <= off /\ off + len <= b + sz))
Proof
  strip_tac >> (
  `lo < off + len \/ op_prov G ops.iao_ofst <> NONE ==>
   ?v b sz. ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b,sz) /\
            b <= off /\ off + len <= b + sz` by
    (gvs[access_ok_def] >> metis_tac[]) >>
  Cases_on `lo < off + len \/ op_prov G ops.iao_ofst <> NONE`
  >- (first_x_assum drule >> strip_tac >> gvs[] >>
      Cases_on `FLOOKUP rv v`
      >- (disj1_tac >>
          qpat_x_assum `!v site. _` (qspecl_then [`v`, `(b,sz)`] mp_tac) >>
          simp[]) >>
      disj2_tac >> PairCases_on `x` >>
      qpat_x_assum `!v e. _` drule >> simp[]) >>
  disj1_tac >> gvs[] >> rpt strip_tac >>
  Cases_on `FLOOKUP rv v` >> gvs[op_prov_def] >>
  qpat_x_assum `!v e. _` drule >> simp[])
QED
