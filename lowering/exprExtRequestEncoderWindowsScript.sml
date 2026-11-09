(* Protected windows at the same exit as the counted encoder law. *)
Theory exprExtRequestEncoderWindows
Ancestors
  exprExtRequestEncoderResource exprExtRequestEncoderWitness
  abiEncoderWindowContract abiCallerLocalScratch
  exprLoweringProps localPtrsProps compileEnv venomMemDefs

Theorem extrequest_encoder_local_scratch:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ local_ptrs_rel func ce scopes s /\
  local_ptrs_reserved ce st /\ local_region ce scopes s name q n /\
  id IN window_alloca_sites func (frag_ids st en) /\
  FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
  venomMemDefs$regions_disjoint (q,n) (b,sz)
Proof
  strip_tac >> gvs[window_alloca_sites_def] >>
  drule_all extrequest_encoder_function_alloca_not_local >>
  disch_then (qspec_then `scopes` strip_assume_tac) >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[compileEnvTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem extrequest_encoder_local_window:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ local_ptrs_rel func ce scopes s /\
  local_ptrs_reserved ce st /\ local_region ce scopes s name q n /\
  abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    outs s t /\ window_alloca_growth s t /\
  EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >> drule_all abi_caller_local_end >> strip_tac >>
  irule window_alloca_growth_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[extrequest_encoder_local_scratch]
QED

Theorem extrequest_encoder_immutable_window:
  immutable_alloca_sep func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc q) /\
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
    name = SOME (tv,v) /\
  abi_encoder_registered_effect (window_alloca_sites func ids) outs s t /\
  window_alloca_growth s t /\
  EVERY (\r. venomMemDefs$regions_disjoint (q,type_memory_size tv) r) outs ==>
  mem_bytes_at q (type_memory_size tv) t.vs_memory =
  mem_bytes_at q (type_memory_size tv) s.vs_memory
Proof
  strip_tac >>
  fs[immutable_alloca_sep_def] >> first_x_assum drule_all >> strip_tac >>
  irule window_alloca_growth_frame >> simp[] >>
  qexistsl_tac [`window_alloca_sites func ids`, `outs`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  gvs[window_alloca_sites_def] >>
  first_x_assum drule_all >>
  simp[compileEnvTheory.regions_disjoint_def,
       venomMemDefsTheory.regions_disjoint_def]
QED

Theorem extrequest_encoder_historical_window:
  alloca_inv s /\ owner < st.cs_next_id /\
  FLOOKUP s.vs_allocas owner = SOME (p,cap) /\
  p <= q /\ q + n <= p + cap /\
  abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    outs s t /\ window_alloca_growth s t /\
  EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs ==>
  mem_bytes_at q n t.vs_memory = mem_bytes_at q n s.vs_memory
Proof
  strip_tac >>
  `p + cap <= s.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  irule window_alloca_growth_frame >> simp[] >>
  qexistsl_tac [`window_alloca_sites func (frag_ids st en)`, `outs`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule extrequest_encoder_registered_window >>
  fs[window_alloca_sites_def] >> metis_tac[]
QED
