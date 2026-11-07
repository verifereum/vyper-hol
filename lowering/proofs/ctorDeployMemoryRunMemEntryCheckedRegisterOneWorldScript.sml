Theory ctorDeployMemoryRunMemEntryCheckedRegisterOneWorld
Ancestors
 ctorDeployMemoryRunMemEntryCheckedArgWorld
 ctorDeployMemoryRunMemEntryCheckedStep
 ctorDeployMemoryRunMemEntryShiftedRegistration
 ctorDeployMemoryRunMemEntryShiftedAlloc
 ctorDeployMemoryRunMemEntryRegistration
 venomExecSemantics abiEncoderProps
 venomMemDefs abiEncoderRegisteredEffect abiDecoderLoop
 context exprLoweringProps emitHelperProps fragExec abiDecoderReentry
 ctorAbiActualSites
 actualAllocCredit actualAllocExec allocaHistory loweringHalt
 ctorAbiActualFrame abiDecoderCounters ctorRegisterArgs ctorArgDecode
 moduleLowering abiEncoder compileVyper localPtrsProps entryArgPtrs fragGasPathMem
 words list rich_list finite_map pred_set arithmetic exprLowering compileEnv venomInst venomState

Theorem ctor_world_alloc_buffer_state_props[local]:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ initial.vs_alloca_next < dimword (:256) /\
 local_ptrs_rel func ce scopes initial /\ fresh_vars_wrt st initial /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 a = (update_var (STRING #"%" (toString st.cs_next_var))
     (n2w initial.vs_alloca_next)
     (initial with <| vs_allocas := initial.vs_allocas |+
       (st.cs_next_id,(initial.vs_alloca_next,n));
       vs_alloca_next := initial.vs_alloca_next+n |>))
     with vs_inst_idx := LENGTH sa.cs_current_insts ==>
 buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
 local_ptrs_rel func ce scopes a /\
 local_backed func (STRING #"%" (toString st.cs_next_var)) a initial.vs_alloca_next n /\
 fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
 (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
 (!name b sz. local_region ce scopes a name b sz ==>
   compileEnv$regions_disjoint initial.vs_alloca_next n b sz) /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x a = SOME w) /\
 abi_encoder_registered_effect (frag_ids st sa) [] initial a
Proof
 strip_tac >>
 `not_scope_ptr ce scopes (STRING #"%" (toString st.cs_next_var))` by
   (irule local_ptrs_rel_fresh_not_scope_ptr >>
    qexistsl [`func`, `initial`, `st`] >> simp[GREATER_EQ]) >>
 `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) =
    OK (a with vs_inst_idx := initial.vs_inst_idx)` by
   gvs[exec_alloca_def, mk_inst_def, update_var_def, w2n_n2w,
       venom_state_component_equality] >>
 drule local_ptrs_rel_exec_alloca_fresh >> simp[mk_inst_def] >>
 disch_then (qspecl_then [`func`, `ce`, `scopes`] mp_tac) >>
 simp[local_ptrs_rel_inst_idx] >> strip_tac >>
 drule compile_alloc_buffer_parts >> strip_tac >> simp[] >>
 conj_tac
 >- (simp[local_backed_def] >> disj1_tac >>
     qexists `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]` >>
     drule_all entry_alloc_buffer_inst >> gvs[mk_inst_def]) >>
 conj_tac
 >- (fs[fresh_vars_wrt_def, update_var_def, GREATER_EQ] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 conj_tac
 >- (simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
     IF_CASES_TAC >> gvs[] >> first_x_assum irule >> decide_tac) >>
 conj_tac
 >- (rpt strip_tac >> qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
 conj_tac
 >- (rpt strip_tac >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> gvs[lookup_var_def]) >>
 simp[abi_encoder_registered_effect_def, frag_ids_def, GSPECIFICATION,
      update_var_def, FLOOKUP_UPDATE] >>
 rpt strip_tac >> IF_CASES_TAC >> gvs[] >>
 `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >> gvs[]
QED

Theorem ctor_checked_alloc_buffer_world_actual_from:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ local_ptrs_rel func ce scopes initial /\
 fresh_vars_wrt st initial /\ alloca_inv initial /\ alloca_history func initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?a. buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
   local_ptrs_rel func ce scopes a /\
   lookup_var (STRING #"%" (toString st.cs_next_var)) a =
     SOME (n2w initial.vs_alloca_next) /\
   local_backed func (STRING #"%" (toString st.cs_next_var)) a initial.vs_alloca_next n /\
   FLOOKUP a.vs_allocas st.cs_next_id = SOME (initial.vs_alloca_next,n) /\
   a.vs_alloca_next = initial.vs_alloca_next+n /\
   a.vs_alloca_next < dimword (:256) /\
   alloca_inv a /\ alloca_frontier_inv_from k ctx func site a /\
   fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
   (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
   (!name b sz. local_region ce scopes a name b sz ==>
     compileEnv$regions_disjoint initial.vs_alloca_next n b sz) /\
   a.vs_memory = initial.vs_memory /\
   a.vs_data_section = initial.vs_data_section /\
   a.vs_call_ctx = initial.vs_call_ctx /\ a.vs_labels = initial.vs_labels /\
   (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
     lookup_var x a = SOME w) /\
   abi_encoder_registered_effect (frag_ids st sa) [] initial a /\
   ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
   a.vs_inst_idx = LENGTH sa.cs_current_insts /\
   abi_decode_sim ctx func initial a /\
   gas_path_mem ctx func initial 0 (OK a) /\
   a.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func a /\
   a.vs_tx_ctx = initial.vs_tx_ctx /\ a.vs_block_ctx = initial.vs_block_ctx /\
   a.vs_outcomes = initial.vs_outcomes
Proof
 strip_tac >>
 `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >>
 drule_all ctor_checked_alloc_buffer_run_from >> strip_tac >>
 `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
 drule_all ctor_world_alloc_buffer_state_props >> strip_tac >>
 qexists `a` >> asm_rewrite_tac[] >>
 gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem ctor_checked_register_one_world_actual_from:
 !r ce env fargs avs atys encoded i name ty entry off data_size old
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
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
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
 actual.vs_outcomes = initial.vs_outcomes
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all ctor_checked_alloc_buffer_world_actual_from >>
 disch_then (qx_choose_then `a` (map_every assume_tac o CONJUNCTS)) >>
 `ce' = ce with ce_vars := ce.ce_vars |+
   (name,PtrVar (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce ty))` by simp[] >>
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
 ntac 10 (pop_last_assum kall_tac) >>
 qpat_x_assum `abi_decoder_coherent ce _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_metadata ce _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_coherent ce' _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_metadata ce' _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `mem_bytes_at _ _ a.vs_data_section = _` kall_tac >>
 suspend "finish"
QED

Resume ctor_checked_register_one_world_actual_from[finish]:
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

Resume ctor_checked_register_one_world_actual_from[locals]:
 qpat_assum `ce' = ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var _) _)`
   (fn th => pure_once_rewrite_tac[th]) >>
 irule ctor_scratch_decode_bind_ptr >>
 conj_tac >- simp[] >>
 qexistsl [`initial.vs_alloca_next`, `entry`, `frag_ids sa st'`, `a`, `sa`,
   `n2w initial.vs_alloca_next : bytes32`] >>
 asm_rewrite_tac[] >>
 `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
 simp[w2n_n2w] >> gnvs[]
QED

Resume ctor_checked_register_one_world_actual_from[effect]:
 irule ctor_registered_alloc_decode_effect >>
 qexistsl [`a`, `st.cs_next_id`, `frag_ids st sa`, `initial.vs_alloca_next`,
   `frag_ids sa st'`, `type_memory_bytes ce' ty`] >>
 asm_rewrite_tac[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Resume ctor_checked_register_one_world_actual_from[registers]:
 rpt strip_tac >>
 `not_fresh_at sa x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 metis_tac[]
QED

Finalise ctor_checked_register_one_world_actual_from
