(* Restore the caller relation from the decoder's actual resource and byte frames. *)
Theory extcallReturnFrameMemory
Ancestors
  abiDecoderSiteEffect actualDecoderSites allocationGrowth fragGasPathFrameMem
  exprSimAbiDecodeLiveFrame exprSimProps exprLoweringProps loweringSlice
  loweringStateRelDefs localPtrsProps compileEnv venomState

Theorem extcall_return_decoder_state_frame:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce st /\
  gas_path_mem ctx func s n (OK t) /\ decode_site_resources ctx func t /\
  allocation_growth s t /\ decode_static_frame s t /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s) /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
      mem_bytes_at off (type_memory_size tv) s.vs_memory) ==>
  stmt_state_rel ctx func ce cx es t /\ locals_kept ce es es s t
Proof
  strip_tac >>
  `state_rel func ce cx es s /\ local_ptrs_rel func ce es.scopes s /\
   immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es s /\
   immutable_alloca_sep func ce cx es s /\ immutable_base_zero ce s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by
       simp[GSYM abi_decode_old_var_live] >>
     qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _`
       (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]) >>
  `!name entry p sz. lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
     lookup_var p t = lookup_var p s` by
    (rpt strip_tac >> first_x_assum irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name b sz. local_region ce es.scopes t name b sz <=>
     local_region ce es.scopes s name b sz` by
    metis_tac[local_region_lookup_cong] >>
  `local_ptrs_rel func ce es.scopes t` by
    (irule local_ptrs_rel_mem_agree >> qexists_tac `s` >>
     fs[allocation_growth_def] >> metis_tac[]) >>
  suspend "immutables"
QED

Resume extcall_return_decoder_state_frame[immutables]:
  `t.vs_data_section = s.vs_data_section /\ t.vs_labels = s.vs_labels` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[gas_path_mem_memory_length] >>
  `immutables_rel ce cx.txn.target ce.ce_module ce.ce_is_ctor es t` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `immutable_alloca_sep func ce cx es t` by
    (irule immutable_alloca_sep_frame >> qexistsl_tac [`s`, `es`] >>
     fs[allocation_growth_def] >> conj_tac
     >- (rpt strip_tac >> disj1_tac >> qexists_tac `id` >> simp[]) >>
     rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid`
     >- (disj2_tac >> metis_tac[]) >>
     PairCases_on `x` >> disj1_tac >> metis_tac[]) >>
  `immutable_base_zero ce t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!x. not_fresh_at st x ==> _` irule >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  suspend "finish"
QED

Resume extcall_return_decoder_state_frame[finish]:
  `state_rel func ce cx es t` by
    (irule state_rel_frame >> simp[] >> qexistsl_tac [`es`, `s`] >> simp[] >>
     fs[decode_static_frame_def, venom_state_component_equality]) >>
  conj_tac
  >- (fs[stmt_state_rel_def, decode_site_resources_def] >> metis_tac[]) >>
  irule locals_kept_regions >> simp[] >> first_assum ACCEPT_TAC
QED

Finalise extcall_return_decoder_state_frame
