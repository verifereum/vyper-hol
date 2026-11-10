Theory ctorDeployLoweringEntryLocalBounds
Ancestors
  ctorDeployLoweringEntryCoordinatedRegister ctorDeployLoweringEntrySeparation
  ctorDeployLoweringEntryCompleteRegister ctorDeployLoweringEntryResourceRegister
  ctorDeployLoweringEntryRegisterSizes abiDecoderLoop
  ctorDeployLoweringEntryCompleteRegisterBoundary abiEncoderRegisteredEffect
  abiEncoderProps loweringHalt entryArgPtrs fragExec finite_map pred_set arithmetic
  compileEnv exprLoweringProps ctorRegisterArgs ctorAbiActualSites ctorAbiActualFrame
  ctorDeployLoweringEntryRegisterRun localPtrsProps abiDecoderCoherence
  abiDecoderContract abiDecoderTypedContract vyperABI words venomInst venomState
  compileVyper moduleLowering rich_list list vyperCompiler exprLowering
  abiDecoderCounters abiDecoderCode fragGasPath

Theorem deploy_ctor_local_lower_bound_preserved:
  !s st func. local_ptrs_rel func ce scopes s /\ fresh_vars_wrt st s /\
  (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w) /\
  (!id b sz. local_region ce scopes s id b sz ==> q <= b) ==>
  (!id b sz. local_region ce scopes t id b sz ==> q <= b)
Proof
  rpt gen_tac >> strip_tac >> ho_match_mp_tac deploy_ctor_local_lower_bound_frame >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `?v. lookup_var p s = SOME v` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `not_fresh_at st p` by
    (fs[not_fresh_at_def, fresh_vars_wrt_def, lookup_var_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!n. _ >= _ ==> _` (qspec_then `n` mp_tac) >>
     fs[GREATER_EQ, FLOOKUP_DEF]) >>
  metis_tac[]
QED

Theorem deploy_ctor_register_one_actual_coordinated_map_bounds_gas_path:
 !q k ce env fargs avs atys encoded i name ty entry off data_size old
  buf sa ce' st st' ctx func site initial keep_bound.
 (keep_bound ==> !aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
 lookup_scopes name [scope] = SOME entry /\
 val_wf entry.type entry.value /\
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 gas_path ctx func initial 0 (OK actual) /\
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 local_ptrs_rel func ce' [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce' [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_alloc_actual_complete_gas_path >>
 disch_then (qx_choose_then `a` (map_every assume_tac o CONJUNCTS)) >>
 `a.vs_allocas = initial.vs_allocas |+
   (st.cs_next_id,(initial.vs_alloca_next,type_memory_bytes ce ty))` by
   (drule_all deploy_ctor_alloc_effect_update >> simp[]) >>
 `!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by
   (drule deploy_ctor_register_alloc_literal_sizes >>
    disch_then drule >> simp[] >> metis_tac[]) >>
 `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b` by
   (rpt gen_tac >> strip_tac >>
    Cases_on `inst.inst_id = st.cs_next_id` >> gvs[FLOOKUP_UPDATE] >>
    metis_tac[]) >>
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
 `mem_bytes_at 0 (LENGTH encoded) a.vs_data_section = encoded` by
   (qpat_assum `a.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
    first_assum ACCEPT_TAC) >>
 drule_all deploy_ctor_decode_constructor_arg_old_prefix_complete_gas_path >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 `keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> q <= b` by
   (strip_tac >>
    `!aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) ==> q <= b` by
      (rpt gen_tac >> simp[FLOOKUP_UPDATE] >> rw[] >> metis_tac[]) >>
    `q <= a.vs_alloca_next` by simp[] >>
    match_mp_tac deploy_ctor_actual_registered_alloca_lower_bound >>
    qexistsl [`func`, `frag_ids sa st'`,
      `[(initial.vs_alloca_next,type_memory_bytes ce' ty)]`, `a`] >>
    asm_rewrite_tac[]) >>
 `!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by
   (rpt gen_tac >> strip_tac >>
    qpat_x_assum `!inst n b sz. _ /\ _ /\ _ /\
      FLOOKUP a.vs_allocas inst.inst_id = SOME (b,sz) ==> _` drule_all >> simp[]) >>
 `!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n` by
   (rpt gen_tac >> strip_tac >>
    irule deploy_ctor_generated_decode_args_literal_sizes >>
    qpat_assum `compile_decode_args ce' [build_positional_arg ce (name,ty)] _ _ _ _ _ = _`
      (irule_at Any) >>
    qpat_assum `ctor_actual_scratch func (frag_ids sa st') 0 a.vs_alloca_next actual`
      (irule_at Any) >>
    qpat_assum `abi_encoder_registered_effect (frag_ids sa st') _ a actual`
      (irule_at Any) >>
    qexistsl [`inst`,`b`] >>
    simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
 `q <= a.vs_alloca_next` by simp[] >>
 `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b` by
   (rpt gen_tac >> strip_tac >>
    irule deploy_ctor_alloca_lower_bound_frame >>
    qpat_assum `ctor_actual_scratch func (frag_ids sa st') 0 a.vs_alloca_next actual`
      (irule_at Any) >>
    qpat_assum `abi_encoder_registered_effect (frag_ids sa st') _ a actual`
      (irule_at Any) >>
    qexistsl [`sz`,`inst`] >>
    simp_tac (srw_ss()) [] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
 `type_memory_bytes ce' ty = type_memory_bytes ce ty` by simp[] >>
 drule compile_alloc_buffer_parts >> strip_tac >>
 `st.cs_next_id <= sa.cs_next_id /\ st.cs_next_var <= sa.cs_next_var` by decide_tac >>
 `sa.cs_next_id <= st'.cs_next_id` by
   (qpat_assum `compile_decode_args ce' [build_positional_arg ce' _] _ _ _ _ _ = _` mp_tac >>
    metis_tac[ctor_decode_args_next_id, pairTheory.SND]) >>
 suspend "local_bounds"
QED

Resume deploy_ctor_register_one_actual_coordinated_map_bounds_gas_path[local_bounds]:
 `!id b sz. local_region ce [scope] a id b sz ==> q <= b` by
   (ho_match_mp_tac (Q.SPECL [`initial`,`st`,`func`] deploy_ctor_local_lower_bound_preserved) >> asm_rewrite_tac[]) >>
 `!id b sz. local_region ce [scope] actual id b sz ==> q <= b` by
   (ho_match_mp_tac (Q.SPECL [`a`,`sa`,`func`] deploy_ctor_local_lower_bound_preserved) >> asm_rewrite_tac[]) >>
 `!id b sz. local_region ce' [scope] actual id b sz ==> q <= b` by
   (ho_match_mp_tac deploy_ctor_local_lower_bound_bind >>
    qexistsl [`ce`,`name`,`STRING #"%" (toString st.cs_next_var)`,
      `type_memory_bytes ce ty`,`initial.vs_alloca_next`] >>
    asm_rewrite_tac[] >> conj_tac >- metis_tac[] >> decide_tac) >>
 suspend "finish"
QED

Resume deploy_ctor_register_one_actual_coordinated_map_bounds_gas_path[finish]:
 `gas_path ctx func initial 0 (OK actual)` by
   (irule (SIMP_RULE std_ss [ADD_CLAUSES]
     (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
    qexists `a` >> simp[]) >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- (
   irule ctor_scratch_decode_bind_ptr >>
   conj_tac >- simp[] >>
   qexistsl [`initial.vs_alloca_next`, `entry`, `frag_ids sa st'`, `a`, `sa`,
     `n2w initial.vs_alloca_next : bytes32`] >>
   asm_rewrite_tac[] >>
   `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
   simp[w2n_n2w] >> gnvs[]) >>
 conj_tac >- (
   irule ctor_registered_alloc_decode_effect >>
   qexistsl [`a`, `st.cs_next_id`, `frag_ids st sa`, `initial.vs_alloca_next`,
     `frag_ids sa st'`, `type_memory_bytes ce' ty`] >>
   asm_rewrite_tac[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
 conj_tac >- (
   rpt strip_tac >>
   `not_fresh_at sa x` by
     (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
   metis_tac[]) >>
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 conj_tac >- decide_tac >>
 reverse conj_tac >- decide_tac >>
 `ctor_actual_scratch func (frag_ids sa st') 0 initial.vs_alloca_next actual` by
   (irule ctor_actual_scratch_subregion >>
    qexistsl [`0`, `a.vs_alloca_next`] >> simp[]) >>
 rpt strip_tac >>
 `mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 a.vs_memory` by
   (irule deploy_ctor_actual_registered_memory_prefix >>
    qexistsl [`func`, `frag_ids sa st'`, `[(initial.vs_alloca_next,type_memory_bytes ce' ty)]`,
      `initial.vs_alloca_next`] >> simp[]) >>
 simp[]
QED
Finalise deploy_ctor_register_one_actual_coordinated_map_bounds_gas_path

Theorem deploy_ctor_register_one_actual_coordinated_local_bounds_gas_path:
 !q k ce env fargs avs atys encoded i name ty entry off data_size old
  buf sa ce' st st' ctx func site initial.
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
 lookup_scopes name [scope] = SOME entry /\
 val_wf entry.type entry.value /\
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 gas_path ctx func initial 0 (OK actual) /\
 local_ptrs_rel func ce' [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce' [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >>
 MATCH_ACCEPT_TAC (deploy_ctor_register_one_actual_coordinated_map_bounds_gas_path |>
   SPEC_ALL |> Q.INST [`keep_bound` |-> `F`] |>
   PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES])
QED

Theorem deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path:
 !rest q k ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial keep_bound.
 (keep_bound ==> !aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 rest = DROP i fargs /\ i <= LENGTH fargs /\
 ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
 (!j. j < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL j fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL j fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
       (EL j avs) entry.value) /\
 compile_register_constructor_args (ce0 with ce_vars := vars)
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE i atys))) data_size st = (ce,st') /\
 local_ptrs_rel func (ce0 with ce_vars := vars) [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region (ce0 with ce_vars := vars) [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 gas_path ctx func initial 0 (OK actual) /\
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 Induct >- (rpt gen_tac >> strip_tac >>
   gvs[build_positional_args_def, compile_register_constructor_args_def, comp_return_def] >>
   qexists `initial` >> simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl, cj 1 gas_path_rules] >>
   rpt conj_tac >> first_assum ACCEPT_TAC) >>
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 PairCases_on `h` >>
 `i < LENGTH fargs` by
   (`LENGTH ((h0,h1)::rest) = LENGTH (DROP i fargs)` by metis_tac[] >>
    fs[LENGTH_DROP] >> decide_tac) >>
 `EL i fargs = (h0,h1) /\ rest = DROP (SUC i) fargs` by
   (qspecl_then [`fargs`, `i`] mp_tac DROP_EL_CONS >>
    (impl_tac >- simp[]) >>
    pure_rewrite_tac[GSYM ADD1] >>
    disch_then (fn th => qpat_assum `_::rest = DROP i fargs`
      (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
 qpat_assum `!j. j < LENGTH fargs ==> _` (qspec_then `i` mp_tac) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `entry` (map_every assume_tac o CONJUNCTS)) >>
 qpat_x_assum `!q k ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial keep_bound. _`
   (mk_asm "suffix_ih") >>
 qpat_x_assum `EVERY (\a. ?off. _) (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 qpat_x_assum `EVERY _ (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 `FLOOKUP (ce0 with ce_vars := vars).ce_vars h0 =
    SOME (MemLoc off (type_memory_bytes (ce0 with ce_vars := vars) h1))` by simp[] >>
 suspend "compile_cons"
QED

Resume deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path[compile_cons]:
 drule ctor_register_cons >>
 disch_then (fn th => qpat_x_assum `compile_register_constructor_args _ _ _ _ st = _`
   (mp_tac o PURE_REWRITE_RULE [SRULE[] th])) >>
 Cases_on `compile_alloc_buffer (type_memory_bytes ce0 h1) st` >>
 rename1 `compile_alloc_buffer _ st = (buf,sa)` >>
 simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
 qmatch_goalsub_abbrev_tac `compile_decode_args next _ _ _ _ _` >>
 Cases_on `compile_decode_args next [build_positional_arg ce0 (h0,h1)]
   (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit (n2w data_size)) 0 sa` >>
 rename1 `compile_decode_args _ _ _ _ _ _ sa = (u,sd)` >>
 Cases_on `u` >>
 simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
 strip_tac >>
 drule_all ctor_registration_code_phases >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all ctor_registration_phi_phases >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `compile_alloc_buffer (type_memory_bytes (ce0 with ce_vars := vars) h1) st = (buf,sa)` by simp[] >>
 `next = ((ce0 with ce_vars := vars) with ce_vars :=
     ((ce0 with ce_vars := vars).ce_vars |+
     (h0,PtrVar buf.buf_operand (type_memory_bytes (ce0 with ce_vars := vars) h1))))` by
   simp[Abbr `next`] >>
 `lookup_scopes h0 [scope] = SOME entry /\
  type_memory_size entry.type <= type_memory_bytes (ce0 with ce_vars := vars) h1 /\
  abi_decoder_coherent (ce0 with ce_vars := vars) env
    (ce0 with ce_vars := vars).ce_struct_fields h1 entry.type /\
  abi_decoder_metadata (ce0 with ce_vars := vars) env h1 entry.type
    (type_to_abi_dec_info (ce0 with ce_vars := vars).ce_struct_fields
      (ce0 with ce_vars := vars) h1) (EL i avs) entry.value` by
   (qpat_assum `EL i fargs = _` (fn th => fs[th])) >>
 `compile_decode_args next [build_positional_arg (ce0 with ce_vars := vars) (h0,h1)]
   (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit (n2w data_size)) 0 sa = ((),sd)` by
   (pure_rewrite_tac[ctor_positional_arg_vars] >> first_assum ACCEPT_TAC) >>
 drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) deploy_ctor_register_one_actual_coordinated_map_bounds_gas_path >>
 disch_then (drule_at (Pat `EL _ _ = _`)) >>
 disch_then (drule_at (Pat `_ = enc _ _`)) >>
 disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
 disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
 disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
 disch_then (qspecl_then [`q`, `env`, `off`, `keep_bound`] mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `middle` (map_every assume_tac o CONJUNCTS)) >>
 suspend "recurse"
QED

Resume deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path[recurse]:
 `!tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys` by
   (Induct >> simp[vyper_to_abi_type_def]) >>
 `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env h1` by
   simp[MAP_COMPOSE, EL_MAP] >>
 `abi_embedded_static_size ce0.ce_struct_fields h1 = abi_member_head_size (EL i atys)` by
   (drule ctor_coherent_head_size >> simp[]) >>
 `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) =
   SUM (MAP abi_member_head_size (TAKE i atys)) +
   abi_embedded_static_size ce0.ce_struct_fields h1` by
   (irule EQ_TRANS >> irule_at Any ctor_canonical_offset_step >> simp[]) >>
 `EVERY (\a. ?off. FLOOKUP
    (vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1))) (FST a) =
    SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest` by
   (qpat_assum `EVERY (\a. ?off. _) rest` mp_tac >>
    qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[EVERY_MEM, MEM_MAP, FLOOKUP_UPDATE] >> rpt strip_tac >>
    first_x_assum drule >> strip_tac >>
    `FST a <> h0` by metis_tac[] >> simp[]) >>
 `compile_register_constructor_args
   (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE (SUC i) atys))) data_size sd = (ce,st')` by
   (qpat_assum `compile_register_constructor_args next _ _ _ sd = _` mp_tac >>
    qpat_assum `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) = _`
      (fn th => pure_rewrite_tac[th]) >>
    simp[Abbr `next`, NoAsms]) >>
 `local_ptrs_rel func
   (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
   [scope] middle` by
   (qpat_assum `local_ptrs_rel func next _ middle` mp_tac >> simp[Abbr `next`, NoAsms]) >>
 `!id b sz. local_region
   (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
   [scope] middle id b sz ==> q <= b` by
   (qpat_assum `!id b sz. local_region next _ middle id b sz ==> _` mp_tac >>
    simp[Abbr `next`, NoAsms]) >>
 `mem_bytes_at 0 (LENGTH encoded) middle.vs_data_section = encoded` by
   (qpat_assum `middle.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
    first_assum ACCEPT_TAC) >>
 `ALL_DISTINCT (MAP FST rest)` by
   (qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[MAP, ALL_DISTINCT]) >>
 suspend "apply_ih"
QED

Resume deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path[apply_ih]:
 asm "suffix_ih" (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `_ = DROP _ _`)) >>
 disch_then (drule_at (Pat `_ = enc _ _`)) >>
 disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
 disch_then (qspecl_then [`q`, `env`, `keep_bound`] mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 asm_x "suffix_ih" kall_tac >>
 `gas_path ctx func initial 0 (OK actual)` by
   (irule (SIMP_RULE std_ss [ADD_CLAUSES]
     (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_then)) >>
    qexists `middle` >> simp[]) >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- suspend "suffix_effect" >>
 conj_tac >- suspend "suffix_registers" >>
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 conj_tac >- suspend "frontier" >>
 suspend "memory"
QED

Resume deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path[suffix_effect]:
 `st.cs_next_id <= sd.cs_next_id` by
   (drule compile_alloc_buffer_parts >> strip_tac >>
    `sa.cs_next_id <= sd.cs_next_id` by
      metis_tac[ctor_decode_args_next_id, pairTheory.SND] >> decide_tac) >>
 `sd.cs_next_id <= st'.cs_next_id` by metis_tac[ctor_registration_next_id] >>
 `frag_ids st sd SUBSET frag_ids st st'` by
   (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
 irule abi_encoder_registered_effect_trans >> qexists `middle` >> conj_tac
 >- (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`frag_ids st sd`, `[]:(num#num) list`] >> simp[]) >>
 irule abi_encoder_registered_effect_enlarge >>
 qexistsl [`frag_ids sd st'`, `[]:(num#num) list`] >> simp[]
QED

Resume deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path[suffix_registers]:
 `st.cs_next_var <= sd.cs_next_var` by
   (drule compile_alloc_buffer_parts >> strip_tac >>
    `sa.cs_next_var <= sd.cs_next_var` by
      metis_tac[ctor_decode_args_vars_mono, abi_decoder_vars_mono_def, pairTheory.SND] >>
    decide_tac) >>
 rpt strip_tac >>
 `not_fresh_at sd x` by
   (qpat_assum `not_fresh_at st x` mp_tac >>
    pure_rewrite_tac[not_fresh_at_def] >> strip_tac >>
    gen_tac >> strip_tac >>
    qpat_x_assum `!n. st.cs_next_var <= n ==> _` irule >> decide_tac) >>
 metis_tac[]
QED

Resume deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path[frontier]:
 qpat_x_assum `initial.vs_alloca_next <= middle.vs_alloca_next` mp_tac >>
 qpat_x_assum `middle.vs_alloca_next <= actual.vs_alloca_next` mp_tac >>
 rpt (pop_last_assum kall_tac) >> decide_tac
QED

Resume deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path[memory]:
 rpt strip_tac >>
 `p < middle.vs_alloca_next` by
   (qpat_x_assum `initial.vs_alloca_next <= middle.vs_alloca_next` mp_tac >>
    qpat_assum `p < initial.vs_alloca_next` mp_tac >>
    rpt (pop_last_assum kall_tac) >> decide_tac) >>
 metis_tac[]
QED
Finalise deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path

Theorem deploy_ctor_register_suffix_actual_coordinated_local_bounds_gas_path:
 !rest q k ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial.
 rest = DROP i fargs /\ i <= LENGTH fargs /\
 ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
 (!j. j < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL j fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL j fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
       (EL j avs) entry.value) /\
 compile_register_constructor_args (ce0 with ce_vars := vars)
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE i atys))) data_size st = (ce,st') /\
 local_ptrs_rel func (ce0 with ce_vars := vars) [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region (ce0 with ce_vars := vars) [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 gas_path ctx func initial 0 (OK actual) /\
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >>
 MATCH_ACCEPT_TAC (deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path |>
   SPEC_ALL |> Q.INST [`keep_bound` |-> `F`] |>
   PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES])
QED

Theorem deploy_ctor_register_args_actual_coordinated_map_bounds_gas_path:
 !q k ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial keep_bound.
 (keep_bound ==> !aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL i fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
       (EL i avs) entry.value) /\
 compile_register_constructor_args ce0 (build_positional_args ce0 fargs)
   0 data_size st = (ce,st') /\
 local_ptrs_rel func ce0 [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce0 [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 gas_path ctx func initial 0 (OK actual) /\
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 irule deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path >> asm_rewrite_tac[] >>
 qexistsl [`atys`, `avs`, `ce0`, `data_size`, `encoded`, `env`, `fargs`, `0`, `fargs`,
   `ce0.ce_vars`] >> simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_register_args_actual_coordinated_local_bounds_gas_path:
 !q k ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial.
 ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL i fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
       (EL i avs) entry.value) /\
 compile_register_constructor_args ce0 (build_positional_args ce0 fargs)
   0 data_size st = (ce,st') /\
 local_ptrs_rel func ce0 [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce0 [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 gas_path ctx func initial 0 (OK actual) /\
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >>
 MATCH_ACCEPT_TAC (deploy_ctor_register_args_actual_coordinated_map_bounds_gas_path |>
   SPEC_ALL |> Q.INST [`keep_bound` |-> `F`] |>
   PURE_REWRITE_RULE [IMP_CLAUSES, AND_CLAUSES])
QED

(* Package environments contain MemLoc entries only, so the initial local
   region bound is vacuous, independently of the source scope and state. *)
Theorem deploy_ctor_target_package_no_local_region:
 !tops use_trans nkeys mut nr rr fname fargs dflts ret body
  target ce pos_args pay nr' key ut body' ret' imm scopes s id b sz.
 set_constructor_package_target target
  (package_constructor tops use_trans nkeys
   (mut,nr,rr,fname,fargs,dflts,ret,body)) =
  (ce,pos_args,pay,nr',key,ut,body',ret') ==>
 ~local_region (ce with ce_imm_alloca := imm) scopes s id b sz
Proof
 rpt gen_tac >>
 simp[set_constructor_package_target_def, package_constructor_def,
      update_cenv_nonreentrant_def] >> strip_tac >> gvs[] >>
 simp[local_region_def, cj 3 build_compile_env_vars]
QED

Theorem deploy_ctor_register_one_actual_coordinated_map_bounds:
 !q k ce env fargs avs atys encoded i name ty entry off data_size old
  buf sa ce' st st' ctx func site initial keep_bound.
 (keep_bound ==> !aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
 lookup_scopes name [scope] = SOME entry /\
 val_wf entry.type entry.value /\
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 local_ptrs_rel func ce' [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce' [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_one_actual_coordinated_map_bounds_gas_path >> strip_tac >>
 qexistsl [`actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_register_one_actual_coordinated_local_bounds:
 !q k ce env fargs avs atys encoded i name ty entry off data_size old
  buf sa ce' st st' ctx func site initial.
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
 lookup_scopes name [scope] = SOME entry /\
 val_wf entry.type entry.value /\
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 local_ptrs_rel func ce' [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce' [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_one_actual_coordinated_local_bounds_gas_path >> strip_tac >>
 qexistsl [`actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_register_suffix_actual_coordinated_map_bounds:
 !rest q k ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial keep_bound.
 (keep_bound ==> !aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 rest = DROP i fargs /\ i <= LENGTH fargs /\
 ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
 (!j. j < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL j fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL j fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
       (EL j avs) entry.value) /\
 compile_register_constructor_args (ce0 with ce_vars := vars)
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE i atys))) data_size st = (ce,st') /\
 local_ptrs_rel func (ce0 with ce_vars := vars) [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region (ce0 with ce_vars := vars) [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_suffix_actual_coordinated_map_bounds_gas_path >> strip_tac >>
 qexistsl [`actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_register_suffix_actual_coordinated_local_bounds:
 !rest q k ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial.
 rest = DROP i fargs /\ i <= LENGTH fargs /\
 ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
 (!j. j < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL j fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL j fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
       (EL j avs) entry.value) /\
 compile_register_constructor_args (ce0 with ce_vars := vars)
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE i atys))) data_size st = (ce,st') /\
 local_ptrs_rel func (ce0 with ce_vars := vars) [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region (ce0 with ce_vars := vars) [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_suffix_actual_coordinated_local_bounds_gas_path >> strip_tac >>
 qexistsl [`actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_register_args_actual_coordinated_map_bounds:
 !q k ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial keep_bound.
 (keep_bound ==> !aid b sz. FLOOKUP initial.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL i fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
       (EL i avs) entry.value) /\
 compile_register_constructor_args ce0 (build_positional_args ce0 fargs)
   0 data_size st = (ce,st') /\
 local_ptrs_rel func ce0 [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce0 [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 (keep_bound ==> !aid b sz. FLOOKUP actual.vs_allocas aid = SOME (b,sz) ==> q <= b) /\
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_args_actual_coordinated_map_bounds_gas_path >> strip_tac >>
 qexistsl [`actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_register_args_actual_coordinated_local_bounds:
 !q k ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial.
 ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL i fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
       (EL i avs) entry.value) /\
 compile_register_constructor_args ce0 (build_positional_args ce0 fargs)
   0 data_size st = (ce,st') /\
 local_ptrs_rel func ce0 [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 q <= initial.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce0 [scope] initial id b sz ==> q <= b) ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory) /\
 q <= actual.vs_alloca_next /\
 (!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   inst.inst_operands = [Lit n] /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
 (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
   FLOOKUP actual.vs_allocas inst.inst_id = SOME (b,sz) ==> q <= b) /\
 (!id b sz. local_region ce [scope] actual id b sz ==> q <= b)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_args_actual_coordinated_local_bounds_gas_path >> strip_tac >>
 qexistsl [`actual`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
