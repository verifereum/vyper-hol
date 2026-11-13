(* Classification-to-frontier arithmetic, shared by reads and writes. *)
Theory lowerDloadRangeFrontier
Ancestors lowerDloadSafetyWriteAssembly lowerDloadRangeTransport
  lowerDloadSafetyRelation lowerDloadSafetyValues lowerDloadSafetyKernel
  ptrDiscipline unitTransformDefs contextCodegenRel list

Theorem ld_classified_range_frontier:
  ((getops = mem_read_ops /\ ranges = source_memory_read_ranges) \/
   (getops = mem_write_ops /\ ranges = source_memory_write_ranges)) /\
  access_ok lo G fn inst s /\ ld_ghost_ok fl A H G /\
  ~in_revert_forward fn s /\ getops inst = SOME ops /\
  MEM (w2n x,n) (ranges inst s) /\
  (op_prov H ops.iao_ofst = NONE ==> x=y) /\
  (!a. op_prov H ops.iao_ofst = SOME a ==> ld_wordrel A (SOME a) x y) /\
  frontier < dimword(:256) /\
  (!k b c sz. FLOOKUP A k = SOME (b,c,sz) ==> c+sz <= frontier) ==>
  n=0 \/ w2n y+n <= frontier \/ y=x
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `n=0` >> simp[] >>
  Cases_on `op_prov H ops.iao_ofst` >- metis_tac[] >>
  rename1 `op_prov H ops.iao_ofst = SOME a` >>
  `ld_wordrel A (SOME a) x y` by metis_tac[] >>
  `?b c sz. FLOOKUP A a = SOME (b,c,sz)` by metis_tac[ld_wordrel_SOME] >>
  `op_prov G ops.iao_ofst = SOME (b,sz)` by
    (qpat_x_assum `ld_ghost_ok _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ld_ghost_ok_def]) >>
     Cases_on `ops.iao_ofst` >> fs[op_prov_def] >> res_tac >>
     gvs[lowerDloadSafetyKernelTheory.ld_erase_def]) >>
  `?v b' sz'. ops.iao_ofst = Var v /\ FLOOKUP G v = SOME (b',sz') /\
              b' <= w2n x /\ w2n x+n <= b'+sz'` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >> simp[access_ok_def] >>
     strip_tac >> gvs[] >>
     metis_tac[optionTheory.SOME_11, optionTheory.NOT_SOME_NONE]) >>
  `b' = b /\ sz' = sz` by gvs[op_prov_def] >>
  `c+sz <= frontier` by metis_tac[] >>
  `b <= w2n x /\ w2n x <= b+sz /\ c+sz < dimword(:256)` by decide_tac >>
  `w2n y = c + (w2n x - b)` by metis_tac[ld_wordrel_site_value] >>
  `w2n y+n <= frontier` suffices_by simp[] >>
  decide_tac
QED

(* A range of the source instruction stays inside the target's frontier when
   the address is the same on both sides: the source's own raw check bounds
   it, the target's allocation frontier is at least the source's, and the
   dynamic region's bounds are shared. *)
Theorem ld_source_range_frontier:
  inst_mem_ok_in_fn fn inst s /\ ~in_revert_forward fn s /\
  (ranges = source_memory_read_ranges \/
   ranges = source_memory_write_ranges) /\
  MEM (off,len) (ranges inst s) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  s.vs_fmp = t.vs_fmp /\ s.vs_initial_fmp = t.vs_initial_fmp ==>
  len = 0 \/ off+len <= t.vs_alloca_next \/
  w2n t.vs_initial_fmp <= off /\ off+len <= w2n t.vs_fmp
Proof
  strip_tac >>
  `inst_mem_below_frontier inst s` by
    metis_tac[inst_mem_ok_in_fn_def, contextCodegenRelTheory.in_revert_forward_def] >>
  `MEM (off,len)
     (source_memory_read_ranges inst s ++ source_memory_write_ranges inst s)` by
    gvs[MEM_APPEND] >>
  fs[inst_mem_below_frontier_def, EVERY_MEM] >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >> decide_tac
QED
