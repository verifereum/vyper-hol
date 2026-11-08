(* State reconstruction at the single counted encoder exit. *)
Theory exprExtRequestEncoderState
Ancestors
  exprExtRequestEncoderEndpoint exprExtRequestEncoderWindows
  exprExtRequestPathFields localPtrsProps loweringSlice compileEnv
  abiEncoderRegisteredEffect abiEncoderWindowContract exprLoweringProps
  exprSimProps exprExtRequestEncoderWitness venomState

Theorem extrequest_encoder_local_ptrs:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  alloca_inv s /\ local_ptrs_rel func ce scopes s /\
  local_ptrs_reserved ce st /\
  (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    outs s t /\ window_alloca_growth s t /\
  (!name q n. local_region ce scopes s name q n ==>
    EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs) ==>
  local_ptrs_rel func ce scopes t
Proof
  strip_tac >> irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
  rpt conj_tac
  >- metis_tac[extrequest_encoder_local_window]
  >- (rpt strip_tac >>
      fs[local_ptrs_reserved_def, local_ptrs_rel_def] >> metis_tac[])
  >- metis_tac[window_alloca_growth_def]
  >- fs[abi_encoder_registered_effect_def]
  >- fs[window_alloca_growth_def] >> first_assum ACCEPT_TAC
QED

Theorem extrequest_encoder_state_rel:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    outs s t /\ window_alloca_growth s t /\
  gas_marked_path F ctx func s 0 (OK t) /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables /\
  LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  (!name q n. local_region ce es.scopes s name q n ==>
    EVERY (\r. venomMemDefs$regions_disjoint (q,n) r) outs) /\
  (ce.ce_is_ctor ==> !name tv v q.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc q) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    EVERY (\r. venomMemDefs$regions_disjoint (q,type_memory_size tv) r) outs) ==>
  state_rel func ce cx es t
Proof
  strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func ce es.scopes s /\
   immutable_alloca_sep func ce cx es s /\
   immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
   state_rel func ce cx es s` by fs[stmt_state_rel_def, state_rel_def] >>
  `local_ptrs_rel func ce es.scopes t` by
    (drule_all extrequest_encoder_local_ptrs >> simp[]) >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >> metis_tac[extrequest_encoder_immutable_window]) >>
  drule extrequest_path_contexts >> strip_tac >>
  irule state_rel_frame >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`es`, `s`] >> fs[abi_encoder_registered_effect_def]
QED

Theorem extrequest_encoder_stmt_resources:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  state_rel func ce cx es t /\
  (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
    outs s t /\ window_alloca_growth s t /\
  alloca_inv t /\ alloca_room ctx func t /\ fmp_room ctx func t /\
  t.vs_labels = s.vs_labels /\
  (!i b k. i IN window_alloca_sites func (frag_ids st en) /\
    FLOOKUP t.vs_allocas i = SOME (b,k) ==> k = 32) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >>
  `immutable_base_zero ce t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, local_ptrs_reserved_def] >>
     rpt strip_tac >>
     `lookup_var x s = SOME 0w` by
       metis_tac[immutable_base_zero_def, eval_operand_def, lookup_var_def] >>
     metis_tac[]) >>
  `immutable_alloca_sep func ce cx es t` by
    (fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
     rpt strip_tac >> first_x_assum drule_all >> strip_tac
     >- (fs[window_alloca_growth_def] >> decide_tac)
     >- (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
         >- (fs[window_alloca_growth_def] >>
             first_x_assum drule_all >>
             simp[compileEnvTheory.regions_disjoint_def]) >>
         `FLOOKUP t.vs_allocas inst.inst_id = SOME x` by
           metis_tac[abi_encoder_registered_effect_allocated] >>
         gvs[] >> metis_tac[]) >>
     `local_ptrs_rel func ce es.scopes s` by fs[state_rel_def] >>
     metis_tac[local_region_frame]) >>
  fs[stmt_state_rel_def] >> rpt strip_tac >>
  Cases_on `inst.inst_id IN window_alloca_sites func (frag_ids st en)`
  >- (`inst.inst_id IN frag_ids st en` by fs[window_alloca_sites_def] >>
      drule_all extrequest_encoder_function_alloca_shape >> strip_tac >>
      gvs[] >> first_x_assum drule_all >>
      simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  `FLOOKUP s.vs_allocas inst.inst_id = SOME (base',sz)` by
    (fs[abi_encoder_registered_effect_def] >> metis_tac[]) >> metis_tac[]
QED

Theorem extrequest_encoder_run_state:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_window_pre ctx func st en dst src ei at av sb cap d s /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  owner < st.cs_next_id /\
  FLOOKUP s.vs_allocas owner = SOME (baddr,sz) /\
  baddr <= p /\ p + n <= baddr + sz /\
  venomMemDefs$regions_disjoint (p,n) (d,LENGTH (enc at av)) /\
  (!name q k. local_region ce es.scopes s name q k ==>
    venomMemDefs$regions_disjoint (q,k) (d,LENGTH (enc at av))) /\
  (ce.ce_is_ctor ==> !name tv v q.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc q) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    venomMemDefs$regions_disjoint (q,type_memory_size tv) (d,LENGTH (enc at av))) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    mem_bytes_at d (LENGTH (enc at av)) t.vs_memory = enc at av /\
    eval_operand out t = SOME (n2w (LENGTH (enc at av))) /\
    stmt_state_rel ctx func ce cx es t /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
       lookup_var x t = SOME w) /\
    abi_encoder_registered_effect (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH (enc at av))] s t /\ window_alloca_growth s t /\
    t.vs_labels = s.vs_labels /\ t.vs_fmp = s.vs_fmp /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_immutables = s.vs_immutables /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    FLOOKUP t.vs_allocas owner = SOME (baddr,sz) /\
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory /\
    (!aid q k. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
      FLOOKUP t.vs_allocas aid = SOME (q,k) /\
      (!a m. q <= a /\ a + m <= q + k /\
        venomMemDefs$regions_disjoint (a,m) (d,LENGTH (enc at av)) ==>
        mem_bytes_at a m t.vs_memory = mem_bytes_at a m s.vs_memory))
Proof
  strip_tac >>
  `fmp_room ctx func s /\ alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all extrequest_encoder_run_resources >> strip_tac >>
  `fn_has_code st en func /\ fn_inst_ids_distinct func` by
    fs[abi_encoder_window_pre_def] >>
  `!name q k. local_region ce es.scopes s name q k ==>
    EVERY (\r. venomMemDefs$regions_disjoint (q,k) r)
      [(d,LENGTH (enc at av))]` by (simp[] >> first_assum ACCEPT_TAC) >>
  `ce.ce_is_ctor ==> !name tv v q.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc q) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    EVERY (\r. venomMemDefs$regions_disjoint (q,type_memory_size tv) r)
      [(d,LENGTH (enc at av))]` by (simp[] >> first_assum ACCEPT_TAC) >>
  `state_rel func ce cx es t` by
    (drule_all extrequest_encoder_state_rel >> simp[]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (drule_all extrequest_encoder_stmt_resources >> simp[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> rpt strip_tac
  >- metis_tac[abi_encoder_registered_effect_allocated] >>
  irule extrequest_encoder_historical_window >>
  simp[] >>
  qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
  qpat_assum `FLOOKUP s.vs_allocas aid = SOME _` (irule_at Any) >> simp[]
QED
