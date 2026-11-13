(* Classification-to-frontier arithmetic, shared by reads and writes. *)
Theory lowerDloadRangeFrontier
Ancestors lowerDloadSafetyWriteAssembly lowerDloadRangeTransport

Theorem ld_classified_range_frontier:
  ((getops = mem_read_ops /\ ranges = source_memory_read_ranges) \/
   (getops = mem_write_ops /\ ranges = source_memory_write_ranges)) /\
  access_ok lo (ld_erase A o_f H) fn inst s /\
  ~in_revert_forward fn s /\ getops inst = SOME ops /\
  MEM (w2n x,n) (ranges inst s) /\
  (op_prov H ops.iao_ofst = NONE ==> x=y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  lo <= frontier /\ frontier < dimword(:256) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= frontier) ==>
  n=0 \/ w2n y+n <= frontier
Proof
  strip_tac >> Cases_on `n=0` >> simp[] >>
  `0 < n` by decide_tac >>
  `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz < dimword(:256)` by
    (rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  `(w2n x+n <= lo /\ y=x) \/
   (?k b c sz delta. FLOOKUP A k = SOME (b,c,sz) /\
     w2n x=b+delta /\ w2n y=c+delta /\ delta+n <= sz)` by
    (gvs[] >>
     FIRST [drule_all ld_read_access_classified,
            drule_all ld_write_access_classified] >>
     metis_tac[arithmeticTheory.ADD_SYM]) >>
  gvs[] >>
  qpat_x_assum `!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= frontier`
    drule >> decide_tac
QED
