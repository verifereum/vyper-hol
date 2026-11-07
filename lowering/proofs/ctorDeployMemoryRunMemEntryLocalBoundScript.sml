Theory ctorDeployMemoryRunMemEntryLocalBound
Ancestors
  ctorDeployMemoryRunMemEntryCheckedRegisterOneWorld
  ctorDeployLoweringEntrySeparation compileEnv localPtrsProps venomState finite_map
  ctorDeployMemoryRunMemEntryCheckedArgWorld ctorDeployMemoryRunMemEntryCheckedStep
  ctorDeployMemoryRunMemEntryShiftedRegistration ctorDeployMemoryRunMemEntryShiftedAlloc
  ctorDeployMemoryRunMemEntryRegistration venomExecSemantics abiEncoderProps
  venomMemDefs abiEncoderRegisteredEffect abiDecoderLoop context exprLoweringProps
  emitHelperProps fragExec abiDecoderReentry ctorAbiActualSites actualAllocCredit
  actualAllocExec allocaHistory loweringHalt ctorAbiActualFrame abiDecoderCounters
  ctorRegisterArgs ctorArgDecode moduleLowering abiEncoder compileVyper entryArgPtrs
  fragGasPathMem words list rich_list pred_set arithmetic exprLowering venomInst

Theorem ctor_local_lower_bound_forward:
  local_ptrs_rel func ce scopes s /\
  (!name b sz. local_region ce scopes s name b sz ==> q <= b) /\
  (!name entry p sz w.
    lookup_scopes name scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==> lookup_var p t = SOME w) ==>
  (!name b sz. local_region ce scopes t name b sz ==> q <= b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  fs[local_region_def, local_ptrs_rel_def] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem ctor_lookup_not_fresh:
  fresh_vars_wrt st s /\ lookup_var p s = SOME w ==> not_fresh_at st p
Proof
  simp[fresh_vars_wrt_def, not_fresh_at_def, lookup_var_def, arithmeticTheory.GREATER_EQ] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  gvs[FLOOKUP_DEF]
QED

Theorem ctor_local_lower_bound_old_vars:
  local_ptrs_rel func ce scopes s /\ fresh_vars_wrt st s /\
  (!name b sz. local_region ce scopes s name b sz ==> q <= b) /\
  (!p w. not_fresh_at st p /\ lookup_var p s = SOME w ==>
    lookup_var p t = SOME w) ==>
  (!name b sz. local_region ce scopes t name b sz ==> q <= b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule ctor_local_lower_bound_forward >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[ctor_lookup_not_fresh]
QED
Theorem ctor_local_lower_bound_bound_vars:
  ce' = ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var p) cap) /\
  local_ptrs_rel func ce scopes a /\ fresh_vars_wrt st a /\
  lookup_var p a = SOME v /\
  (!id b sz. local_region ce' scopes a id b sz ==> q <= b) /\
  (!x w. not_fresh_at st x /\ lookup_var x a = SOME w ==>
    lookup_var x t = SOME w) ==>
  (!id b sz. local_region ce' scopes t id b sz ==> q <= b)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[local_region_def, FLOOKUP_UPDATE] >>
  Cases_on `id = name` >> gvs[]
  >- (`not_fresh_at st p` by metis_tac[ctor_lookup_not_fresh] >>
      `lookup_var p t = SOME v` by metis_tac[] >> gvs[] >> metis_tac[]) >>
  fs[local_ptrs_rel_def] >>
  `?w0. lookup_var p' a = SOME w0` by metis_tac[] >>
  `not_fresh_at st p'` by metis_tac[ctor_lookup_not_fresh] >>
  `lookup_var p' t = SOME w0` by metis_tac[] >> gvs[] >> metis_tac[]
QED


Theorem ctor_checked_register_one_world_bound_from:
 !q r ce env fargs avs atys encoded i name ty entry off data_size old
  buf sa ce' st st' ctx func site initial.
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\ EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\ LENGTH encoded <= LENGTH initial.vs_data_section /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
 lookup_scopes name [scope] = SOME entry /\ val_wf entry.type entry.value /\
 type_memory_size entry.type <= type_memory_bytes ce ty /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty entry.type /\
 abi_decoder_metadata ce env ty entry.type
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) entry.value /\
 type_memory_bytes ce ty < dimword (:256) /\
 compile_alloc_buffer (type_memory_bytes ce ty) st = (buf,sa) /\
 ce' = (ce with ce_vars := ce.ce_vars |+
   (name,PtrVar buf.buf_operand (type_memory_bytes ce ty))) /\
 compile_decode_args ce' [build_positional_arg ce (name,ty)] off
   DLOAD (Lit (n2w data_size)) 0 sa = ((),st') /\
 local_ptrs_rel func ce [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st sa func /\ fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
 (sa.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\
 alloca_history func initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!id b sz. local_region ce [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 local_ptrs_rel func ce' [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from r ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 gas_path_mem ctx func initial 0 (OK actual) /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_outcomes = initial.vs_outcomes /\
 (!id b sz. local_region ce' [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all ctor_checked_alloc_buffer_world_actual_from >>
 disch_then (qx_choose_then `a` (map_every assume_tac o CONJUNCTS)) >>
 `!id b sz. local_region ce [scope] a id b sz ==> q <= b` by
   (rpt strip_tac >> irule ctor_local_lower_bound_old_vars >>
    goal_assum (drule_at Any) >> metis_tac[]) >>
 `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
 `ce' = ce with ce_vars := ce.ce_vars |+
   (name,PtrVar (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce ty))` by simp[] >>
 `!id b sz. local_region ce' [scope] a id b sz ==> q <= b` by
   (rpt strip_tac >> irule deploy_ctor_local_lower_bound_bind >>
    goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
 `abi_decoder_coherent ce' env ce'.ce_struct_fields ty entry.type /\
  abi_decoder_metadata ce' env ty entry.type
    (type_to_abi_dec_info ce'.ce_struct_fields ce' ty) (EL i avs) entry.value` by simp[] >>
 `compile_decode_args ce' [build_positional_arg ce' (name,ty)] off
     DLOAD (Lit (n2w data_size)) 0 sa = ((),st')` by gnvs[] >>
 `FLOOKUP ce'.ce_vars name = SOME (PtrVar
   (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce' ty))` by simp[FLOOKUP_UPDATE] >>
 `initial.vs_alloca_next + type_memory_bytes ce' ty <= a.vs_alloca_next` by simp[] >>
 `mem_bytes_at 0 (LENGTH encoded) a.vs_data_section = encoded /\
  LENGTH encoded <= LENGTH a.vs_data_section` by metis_tac[] >>
 drule_all (BETA_RULE ctor_checked_decode_constructor_arg_world_from) >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 `type_memory_bytes ce' ty = type_memory_bytes ce ty` by simp[] >>
 suspend "finish"
QED

Resume ctor_checked_register_one_world_bound_from[finish]:
 `!id b sz. local_region ce' [scope] actual id b sz ==> q <= b` by
   (rpt strip_tac >> irule ctor_local_lower_bound_bound_vars >>
    goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
    metis_tac[]) >>
 ntac 10 (pop_last_assum kall_tac) >>
 qpat_x_assum `abi_decoder_coherent ce _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_metadata ce _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_coherent ce' _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_metadata ce' _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `mem_bytes_at _ _ a.vs_data_section = _` kall_tac >>
 drule compile_alloc_buffer_parts >> strip_tac >>
 `st.cs_next_id <= sa.cs_next_id /\ st.cs_next_var <= sa.cs_next_var` by decide_tac >>
 `sa.cs_next_id <= st'.cs_next_id` by
   (qpat_assum `compile_decode_args ce' [build_positional_arg ce' _] _ _ _ _ _ = _` mp_tac >>
    metis_tac[ctor_decode_args_next_id, pairTheory.SND]) >>
 `gas_path_mem ctx func initial 0 (OK actual)` by
   metis_tac[ctor_checked_path_append, ADD_0] >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- suspend "locals" >>
 conj_tac >- suspend "effect" >>
 conj_tac >- suspend "registers" >>
 metis_tac[abi_decode_sim_trans]
QED

Resume ctor_checked_register_one_world_bound_from[locals]:
 qpat_assum `ce' = ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var _) _)`
   (fn th => pure_once_rewrite_tac[th]) >>
 irule ctor_scratch_decode_bind_ptr >>
 conj_tac >- simp[] >>
 qexistsl [`initial.vs_alloca_next`, `entry`, `frag_ids sa st'`, `a`, `sa`,
   `n2w initial.vs_alloca_next : bytes32`] >>
 asm_rewrite_tac[] >> simp[w2n_n2w] >> gnvs[]
QED

Resume ctor_checked_register_one_world_bound_from[effect]:
 irule ctor_registered_alloc_decode_effect >>
 qexistsl [`a`, `st.cs_next_id`, `frag_ids st sa`, `initial.vs_alloca_next`,
   `frag_ids sa st'`, `type_memory_bytes ce' ty`] >>
 asm_rewrite_tac[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Resume ctor_checked_register_one_world_bound_from[registers]:
 rpt strip_tac >>
 `not_fresh_at sa x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 metis_tac[]
QED

Finalise ctor_checked_register_one_world_bound_from
