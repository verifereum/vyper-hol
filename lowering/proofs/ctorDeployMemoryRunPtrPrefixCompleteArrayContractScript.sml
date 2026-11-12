(* Compiled dynamic-array loop case of the complete paired decoder contract. *)
Theory ctorDeployMemoryRunPtrPrefixCompleteArrayContract
Ancestors
  loweringStateRelDefs
  ctorDeployMemoryRunPtrPrefixCompleteArrayBaseline
  ctorDeployMemoryRunPtrPrefixCompleteCode
  ctorDeployLoweringEntryCompleteArray ctorDeployLoweringEntryArrayOps
  ctorAbiActualArrayLayout ctorAbiActualArrayContext ctorAbiActualArrayEntry
  ctorAbiActualSites ctorAbiActualMemory ctorAbiActualChildFrame ctorAbiActualFrame
  abiDecoderArraySetupInputs abiDecoderContract abiDecoderReentry abiDecoderCoherence
  abiDecoderCorrectPrimitiveArray ctorAbiActualArrayRun
  ctorDeployLoweringEntryArrayFrame exprLowering
  abiDecoderArrayLoopInit abiDecoderIndexInit abiDecoderTypedContract
  abiDecoderRecursiveLoopContext abiDecoderDynamicLoopSetup
  abiDecoderLoopSetup abiDecoderArraySetupCode abiDecoderArrayPrefix
  abiDecoderArrayInvariant abiDecoderRecursiveLoopLayout abiDecoderRecursiveLoopEntry
  abiDecoderExecution abiEncoderRegisteredEffect abiDecoderLoop
  ctorDeployMemoryFrontier allocaFrontierBound valueEncoding valueEncodingProps
  compileEnv venomState venomInst venomExecSemantics venomMemDefs
  ptrDiscipline ptrSafeRun words list rich_list arithmetic finite_map pred_set

val CshiftCode = ``\ty tv.
 !dst src st st' ctx func site initial limit_st sb d D N ids av v root_di
  G tn b sz Ddead lo PG.
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
   (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb.
    lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\
 d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\
 lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x initial) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\
 DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
    val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
                           op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)``;

Theorem prefix_complete_array_scratch_enlarge[local]:
 small SUBSET ids /\ ctor_actual_scratch func small D N final /\
 abi_encoder_registered_effect (ctor_actual_sites func small) regions initial final /\
 ctor_actual_scratch func ids D N initial ==>
 ctor_actual_scratch func ids D N final
Proof
 strip_tac >> simp_tac bool_ss [ctor_actual_scratch_def] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 Cases_on `inst.inst_id IN small`
 >- (qpat_x_assum `ctor_actual_scratch func small _ _ final` mp_tac >>
     simp_tac bool_ss [ctor_actual_scratch_def] >>
     disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
 `inst.inst_id NOTIN ctor_actual_sites func small` by simp[ctor_actual_sites_def] >>
 qpat_x_assum `abi_encoder_registered_effect _ _ initial final` mp_tac >>
 simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
 `FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
 qpat_x_assum `ctor_actual_scratch func ids _ _ initial` mp_tac >>
 simp_tac bool_ss [ctor_actual_scratch_def] >>
 disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]
QED

val Ok = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

Theorem prefix_complete_array_exit_staged[local]:
 (^CshiftCode) ty tv ==>
 abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops (Var slot_var) src (Var dst_var)
   DLOAD (Lit 0w) (Lit 0w) hdr exit_lbl hid header_var first last idlo idhi loop_st.cs_next_var limit_st header_st.cs_next_id ==>
 abi_decode_dynarray_checked_prefix src DLOAD (Lit 0w) maxn asz st = ((),guard_st) ==>
 abi_decode_array_header (Var dst_var) src DLOAD guard_st = (cnt,header_st) ==>
 abi_decode_index_init header_st = (Var slot_var,loop_st) ==>
 lookup_block loop_st.cs_current_bb func.fn_blocks = SOME entry_bb ==>
 entry_bb.bb_instructions = loop_st.cs_current_insts ++ [mk_inst jump_id JMP [Label hdr] []] ==>
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst_var) initial = SOME (n2w d) /\ d < dimword (:256) /\
 abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
 LENGTH vs <= maxn /\ maxn < dimword (:256) /\
 abi_decoder_operand_live st.cs_next_var src /\
 abi_decoder_operand_live st.cs_next_var (Var dst_var) /\
 loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
 header_st.cs_next_id IN ctor_actual_sites func ids /\
 ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d+32 <= D+N /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
 fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
 fn_has_code header_st loop_st func /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst_var = SOME (b,sz) /\ b <= d /\
 d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst_var) = {} /\
 allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
 abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
 abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn))) (ListV avs) (ArrayV (DynArrayV vs)) /\
 sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
 d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) initial.vs_data_section =
   enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
 lo <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
 frag_ids body_st end_st SUBSET ids /\ header_st.cs_next_id NOTIN frag_ids middle end_st ==>
 ?actual Hout qout A slot.
   (!x. abi_decoder_older_vars st.cs_next_var x ==>
     lookup_var x actual = lookup_var x initial) /\
   (^Ok) k ctx func site ids D N d (type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
     st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial (LENGTH vs) (LENGTH vs) actual /\
   ~actual.vs_halted /\ actual.vs_current_bb = exit_lbl /\ actual.vs_inst_idx = 0 /\
   allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
   FLOOKUP Hout slot_var = SOME (slot,32) /\ FLOOKUP Hout dst_var = SOME (b,sz) /\
   op_taint qout (Var slot_var) = {} /\ op_taint qout (Var dst_var) = {} /\ op_taint qout src = {} /\
   FINITE A /\ A SUBSET range_bytes [(d,32+LENGTH vs*type_memory_size tv)] /\ DISJOINT A qout.t_mem /\
   val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
   (!mem. (!a. a IN A ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
     val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d mem) /\
   qout.t_mem SUBSET tn.t_mem /\ qout.t_stor = tn.t_stor /\
   qout.t_trans = tn.t_trans /\ qout.t_imm = tn.t_imm /\
   (!x. abi_decoder_older_vars st.cs_next_var x ==>
     FLOOKUP Hout x = FLOOKUP G x /\ op_taint qout (Var x) = op_taint tn (Var x)) /\
   (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
   actual.vs_code = initial.vs_code /\ actual.vs_gas_readings = initial.vs_gas_readings /\
   actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
   actual.vs_block_ctx = initial.vs_block_ctx /\ abi_decode_sim ctx func initial actual /\
   ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG Hout qout actual) ==>
     !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)
Proof
 disch_then (mp_tac o MATCH_MP prefix_complete_array_initial_exit_pair_exact) >>
 rpt strip_tac >> first_x_assum irule >> asm_rewrite_tac[]
QED

Theorem prefix_dynamic_array_loop_complete_code_contract:
 (^CshiftCode) ty tv /\
 (is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^CshiftCode) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") assume_tac) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn) st = ((),st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [Once type_to_abi_dec_info_def]) >>
 drule_all ctor_actual_array_loop_layout >> strip_tac >>
 drule_all (ctor_actual_array_prefix_inputs |> Q.INST [`hi` |-> `Lit 0w`] |> SIMP_RULE bool_ss []) >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst)` by
   (Cases_on `src` >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `loop_st.cs_next_var <= limit_st.cs_next_var` by
   fs[abi_decoder_recursive_loop_compiled_def] >>
 `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d+32 <= D+N` by
   fs[Once type_memory_bytes_def] >>
 `d < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> fs[]) >>
 `ctor_actual_scratch func (frag_ids st st') D N initial` by
   (irule ctor_actual_scratch_restrict >> goal_assum (drule_at Any) >> simp[]) >>
 `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
   (irule ctor_actual_function_ids >> simp[]) >>
 `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> simp[]) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule abi_decode_index_init_shape >> strip_tac >>
 qpat_x_assum `ip = Var _` SUBST_ALL_TAC >>
 drule_all abi_decoder_loop_phase_entry >> disch_tac >>
 `d < dimword (:256) /\ lo <= initial.vs_alloca_next /\
  d+32 <= D+N` by fs[] >>
 `loop_st.cs_next_var <= limit_st.cs_next_var` by simp[] >>
 `?entry_bb. lookup_block loop_st.cs_current_bb func.fn_blocks = SOME entry_bb /\
   entry_bb.bb_instructions = loop_st.cs_current_insts ++
     [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]` by simp[] >>
 pop_assum strip_assume_tac >>
 asm "child" (drule o GEN_ALL o MATCH_MP prefix_complete_array_exit_staged) >>
 disch_then drule >> disch_then drule >> disch_then drule >>
 disch_then drule >> disch_then drule >>
 disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
 disch_then (drule_all o Q.INST [`ids` |-> `frag_ids st st'`] o SPEC_ALL) >>
 disch_then (qspecl_then [`PG`, `Ddead`] strip_assume_tac) >>
 qpat_assum `(^Ok) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
   (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
 `ctor_actual_scratch func ids D N actual` by
   (irule prefix_complete_array_scratch_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
 drule abi_decoder_array_setup_head >> strip_tac >>
 qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
 asm_rewrite_tac[] >> disch_then (mp_tac o MATCH_MP abi_decoder_loop_suffix_facts) >> strip_tac >>
 qexistsl [`actual`, `Hout`, `qout`, `A`] >>
 asm_simp_tac bool_ss [LENGTH] >>
 reverse conj_tac
 >- (reverse conj_tac
     >- (simp_tac bool_ss [not_fresh_at_def] >>
         qpat_x_assum `!x. abi_decoder_older_vars _ x ==> _` mp_tac >>
         simp[abi_decoder_older_vars_def]) >>
     irule SUBSET_TRANS >>
     qexists `range_bytes [(d,32 + LENGTH vs * type_memory_size tv)]` >>
     conj_tac >- simp[] >>
     `type_memory_bytes ce ty = type_memory_size tv` by
       (drule (iffLR abi_decoder_coherent_array_iff) >> strip_tac >> gvs[] >>
        drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
     fs[Once type_memory_bytes_def, range_bytes_def, SUBSET_DEF] >>
     rpt strip_tac >> fs[] >>
     `LENGTH vs * type_memory_size tv <= maxn * type_memory_size tv` by
       simp[LESS_MONO_MULT] >> decide_tac) >>
 simp_tac bool_ss [not_fresh_at_def] >>
 qpat_x_assum `!x. abi_decoder_older_vars _ x ==> lookup_var x actual = _` mp_tac >>
 simp[abi_decoder_older_vars_def]
QED

val _ = export_theory();
