Theory exprSimAbiEncodeProducerBoundary
Ancestors
  exprSimHash localPtrsProps allocaSiteResource compileEnv venomMemDefs
  venomState venomInst list words
  exprSimHashBoundary

Theorem abi_encode_expr_footprint_site_disjoint:
  expr_val_at ce cx ty sa sm es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s = SOME w /\ alloca_inv s /\
  fn_inst_ids_distinct func /\ local_ptrs_rel func ce es.scopes s /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr ce es.scopes q /\ sm.cs_next_id <= inst.inst_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (w2n w,val_footprint tv v) (b,sz)
Proof
  strip_tac >> drule_all expr_val_at_footprint >> strip_tac
  >- (`aid <> inst.inst_id` by decide_tac >>
      `venomMemDefs$regions_disjoint (b',sz') (b,sz)` by
        (irule alloca_site_registered_disjoint >>
         goal_assum (drule_at Any) >> metis_tac[]) >>
      gvs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac)
  >- (drule_all local_ptrs_rel_alloca_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def,
        venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[venomMemDefsTheory.regions_disjoint_def]
QED
