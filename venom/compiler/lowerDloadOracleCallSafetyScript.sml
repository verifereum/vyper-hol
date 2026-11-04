(* Current-instruction range safety does not require successful execution. *)
Theory lowerDloadOracleCallSafety
Ancestors
  lowerDloadOracleCallAssembly lowerDloadSafetyAllocBounds
  lowerDloadSafetyAmbient lowerDloadSafetyValues lowerDloadSafetyRelation lowerDloadSafetyKernel
  unitMemInv unitTransformDefs memLocDefs ptrDiscipline
  finite_map pred_set list words arithmetic

Theorem ld_alloc_target_frontier:
  ld_global lo A frames /\ FDOM A = ld_slots A frames /\
  EVERY (ld_maps A) frames /\ FLOOKUP A k = SOME (b,c,n) ==>
  c+n <= (HD frames).lf_tgt.vs_alloca_next
Proof
  strip_tac >> drule_all ld_slot_source_site >> strip_tac >>
  `ld_maps A (EL j frames)` by gvs[EVERY_EL] >>
  `FLOOKUP (EL j frames).lf_src.vs_allocas aid = SOME (b,n)` by
    gvs[ld_sites_def] >>
  `FLOOKUP (EL j frames).lf_tgt.vs_allocas aid = SOME (c,n)` by
    (gvs[ld_maps_def] >>
     qpat_x_assum `!aid b n. FLOOKUP _ aid = SOME (b,n) ==> ?c. _ /\ _`
       drule >> strip_tac >> gvs[]) >>
  `(j,aid,c,n) IN ld_sites frames F` by
    (simp[ld_sites_def] >> metis_tac[]) >>
  drule_all ld_global_bounds >> simp[]
QED
