Theory ctorDeployMemoryRunMemEntryCheckedRegistrationWorld
Ancestors
 ctorDeployMemoryRunMemEntryCheckedRegisterOneWorld
 ctorDeployMemoryRunMemEntryCheckedStep
 ctorDeployMemoryRunMemEntryShiftedRegistration
 ctorDeployMemoryRunMemEntryRegistration
 abiDecoderCoherence abiEncoderProps valueEncoding contractABI vyperABI
 venomMemDefs abiEncoderRegisteredEffect abiDecoderLoop
 context exprLoweringProps emitHelperProps fragExec abiDecoderReentry
 ctorAbiActualSites allocaHistory loweringHalt ctorAbiActualFrame
 abiDecoderCounters ctorRegisterArgs ctorArgDecode
 moduleLowering abiEncoder compileVyper localPtrsProps entryArgPtrs fragGasPathMem
 words list rich_list finite_map pred_set arithmetic exprLowering compileEnv venomInst venomState

Theorem ctor_checked_selected_type_world[local]:
 i < LENGTH fargs /\ EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) ==>
 LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env ty
Proof
 `!tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys` by
   (Induct >> simp[vyper_to_abi_type_def]) >>
 simp[MAP_COMPOSE, EL_MAP]
QED

Theorem ctor_checked_register_suffix_world_actual_from:
 !rest r ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial.
 rest = DROP i fargs /\ i <= LENGTH fargs /\
 ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\ LENGTH encoded <= LENGTH initial.vs_data_section /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
 (!j. j < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields (SND (EL j fargs)) entry.type /\
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
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\
 alloca_history func initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
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
 actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_outcomes = initial.vs_outcomes
Proof
 Induct >- (rpt gen_tac >> strip_tac >>
   gvs[build_positional_args_def, compile_register_constructor_args_def, comp_return_def] >>
   qexists `initial` >> simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl] >>
   irule (cj 1 gas_path_mem_rules) >> simp[]) >>
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 PairCases_on `h` >>
 `i < LENGTH fargs` by
   (`LENGTH ((h0,h1)::rest) = LENGTH (DROP i fargs)` by metis_tac[] >>
    fs[LENGTH_DROP] >> decide_tac) >>
 `EL i fargs = (h0,h1) /\ rest = DROP (SUC i) fargs` by
   (qspecl_then [`fargs`, `i`] mp_tac DROP_EL_CONS >>
    (impl_tac >- simp[]) >> pure_rewrite_tac[GSYM ADD1] >>
    disch_then (fn th => qpat_assum `_::rest = DROP i fargs`
      (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
 qpat_assum `!j. j < LENGTH fargs ==> _` (qspec_then `i` mp_tac) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `entry` (map_every assume_tac o CONJUNCTS)) >>
 qpat_x_assum `!r ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial. _`
   (mk_asm "suffix_ih") >>
 qpat_x_assum `EVERY (\a. ?off. _) (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 qpat_x_assum `EVERY _ (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 `FLOOKUP (ce0 with ce_vars := vars).ce_vars h0 =
    SOME (MemLoc off (type_memory_bytes (ce0 with ce_vars := vars) h1))` by simp[] >>
 suspend "phases"
QED

Resume ctor_checked_register_suffix_world_actual_from[phases]:
 drule ctor_register_cons >>
 disch_then (fn th => qpat_x_assum `compile_register_constructor_args _ _ _ _ st = _`
   (mp_tac o PURE_REWRITE_RULE [SRULE[] th])) >>
 Cases_on `compile_alloc_buffer (type_memory_bytes ce0 h1) st` >>
 rename1 `compile_alloc_buffer _ st = (buf,sa)` >>
 simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
 qmatch_goalsub_abbrev_tac `compile_decode_args next _ _ _ _ _` >>
 Cases_on `compile_decode_args next [build_positional_arg ce0 (h0,h1)]
   (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit (n2w data_size)) 0 sa` >>
 rename1 `compile_decode_args _ _ _ _ _ _ sa = (u,sd)` >> Cases_on `u` >>
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
 drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) ctor_checked_register_one_world_actual_from >>
 disch_then (drule_at (Pat `EL _ _ = _`)) >>
 disch_then (drule_at (Pat `_ = enc _ _`)) >>
 disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
 disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
 disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
 disch_then (qspecl_then [`env`, `off`] mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `middle` (map_every assume_tac o CONJUNCTS)) >>
 suspend "recurse"
QED

Resume ctor_checked_register_suffix_world_actual_from[recurse]:
 `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env h1` by
   (irule ctor_checked_selected_type_world >> goal_assum (drule_at Any) >> simp[]) >>
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
    first_x_assum drule >> strip_tac >> `FST a <> h0` by metis_tac[] >> simp[]) >>
 `compile_register_constructor_args
   (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE (SUC i) atys))) data_size sd = (ce,st')` by
   (qpat_assum `compile_register_constructor_args next _ _ _ sd = _` mp_tac >>
    qpat_assum `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) = _`
      (fn th => pure_rewrite_tac[th]) >> simp[Abbr `next`, NoAsms]) >>
 `local_ptrs_rel func
   (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
   [scope] middle` by
   (qpat_assum `local_ptrs_rel func next _ middle` mp_tac >> simp[Abbr `next`, NoAsms]) >>
 `mem_bytes_at 0 (LENGTH encoded) middle.vs_data_section = encoded /\
  LENGTH encoded <= LENGTH middle.vs_data_section` by
   (qpat_assum `middle.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
    asm_rewrite_tac[]) >>
 `ALL_DISTINCT (MAP FST rest)` by
   (qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[MAP, ALL_DISTINCT]) >>
 asm "suffix_ih" (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `_ = DROP _ _`)) >>
 disch_then (drule_at (Pat `_ = enc _ _`)) >>
 disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
 disch_then (qspec_then `env` mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 asm_x "suffix_ih" kall_tac >> suspend "finish"
QED

Resume ctor_checked_register_suffix_world_actual_from[finish]:
 `gas_path_mem ctx func initial 0 (OK actual)` by
   metis_tac[ctor_checked_path_append, ADD_0] >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- suspend "suffix_effect" >>
 conj_tac >- suspend "suffix_registers" >>
 metis_tac[abi_decode_sim_trans]
QED

Resume ctor_checked_register_suffix_world_actual_from[suffix_effect]:
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

Resume ctor_checked_register_suffix_world_actual_from[suffix_registers]:
 `st.cs_next_var <= sd.cs_next_var` by
   (drule compile_alloc_buffer_parts >> strip_tac >>
    `sa.cs_next_var <= sd.cs_next_var` by
      metis_tac[ctor_decode_args_vars_mono, abi_decoder_vars_mono_def, pairTheory.SND] >>
    decide_tac) >>
 rpt strip_tac >>
 `not_fresh_at sd x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 metis_tac[]
QED

Finalise ctor_checked_register_suffix_world_actual_from

Theorem ctor_checked_register_args_world_from:
 !r ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial.
 ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\ LENGTH encoded <= LENGTH initial.vs_data_section /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields (SND (EL i fargs)) entry.type /\
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
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\
 alloca_history func initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
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
 actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_outcomes = initial.vs_outcomes
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 irule ctor_checked_register_suffix_world_actual_from >> asm_rewrite_tac[] >>
 qexistsl [`atys`, `avs`, `ce0`, `data_size`, `encoded`, `env`, `fargs`, `0`, `fargs`,
   `ce0.ce_vars`] >> simp[]
QED
