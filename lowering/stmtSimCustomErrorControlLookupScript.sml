(* Exact function lookup for realized chronological instruction chunks. *)
Theory stmtSimCustomErrorControlLookup
Ancestors
  stmtSimCustomErrorControl stmtSimCustomErrorRegion fragExec list rich_list
  pred_set venomExecSemantics venomInst

Theorem ce_chunks_finished_lookup:
  ce_chunks a b C /\ fn_has_code a b func ==>
  !c. MEM c (FRONT (ce_prepend a.cs_current_insts C)) ==>
    lookup_block (FST c) func.fn_blocks = SOME (ce_block c)
Proof
  strip_tac >>
  `emitted_blocks a b =
    REVERSE (MAP ce_block (FRONT (ce_prepend a.cs_current_insts C)))` by
    (irule emitted_blocks_append >> fs[ce_chunks_def]) >>
  fs[fn_has_code_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `ce_block c` mp_tac) >>
  simp[MEM_MAP, MEM_REVERSE] >>
  impl_tac >- (qexists_tac `c` >> simp[]) >>
  Cases_on `c` >> simp[ce_block_def]
QED

Theorem ce_chunks_all_lookup:
  ce_chunks a b C /\ fn_has_code a b func ==>
  !c. MEM c (ce_prepend a.cs_current_insts C) ==>
    ?bb. lookup_block (FST c) func.fn_blocks = SOME bb /\
         isPREFIX (SND c) bb.bb_instructions
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `ce_prepend a.cs_current_insts C <> []` by
    (Cases_on `C` >> fs[ce_chunks_def, ce_prepend_def] >>
     PairCases_on `h` >> simp[ce_prepend_def]) >>
  Cases_on `MEM c (FRONT (ce_prepend a.cs_current_insts C))`
  >- (drule_all ce_chunks_finished_lookup >>
      strip_tac >> qexists_tac `ce_block c` >>
      Cases_on `c` >> simp[ce_block_def]) >>
  `c = LAST (ce_prepend a.cs_current_insts C)` by
    metis_tac[APPEND_FRONT_LAST, MEM_APPEND, MEM] >>
  fs[fn_has_code_def, ce_chunks_def] >>
  Cases_on `C` >> fs[ce_prepend_def] >> PairCases_on `h` >>
  Cases_on `t` >> gvs[ce_prepend_def] >> metis_tac[]
QED
