(* Shifted registration decoder with the full complete-code frame. *)
Theory ctorDeployMemoryRunPtrPrefixEntryRegisterDecode
Ancestors
  loweringStateRelDefs
 ctorDeployMemoryRunPtrPrefixCompleteCoherent
 ctorDeployMemoryRunPtrPrefixEntryRegisterAddress
 ctorDeployMemoryRunPtrPrefixRegisterOne
 ctorRegisterArgs abiDecoderCode abiDecoderContract abiEncoderRegisteredEffect
 abiDecoderCoherence abiDecoderCounters ctorAbiActualFrame abiDecoderLoop
 abiEncoderProps emitHelperProps fragExec compileEnv
 localPtrsProps entryArgPtrs loweringHalt moduleLowering context venomInst venomExecSemantics
 allocaFrontierBound allocaBudgetProps venomMemDefs ctorAbiActualSites ctorDeployMemoryFrontier
 ptrSafeRun ptrDiscipline venomState finite_map words arithmetic pred_set list rich_list

Theorem prefix_entry_register_decode_paired:
 compile_abi_decode_to_buf (Var dst) src DLOAD (Lit 0w) (Lit 0w)
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),last) /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand (Var dst) initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (!x. src = Var x \/ Var dst = Var x \/ Lit 0w = Var x ==> not_fresh_at st x) /\
 fresh_vars_wrt st initial /\ fn_has_code st last func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next /\ lo <= d ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st last))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st last) 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt last actual /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = last.cs_current_bb /\
 actual.vs_inst_idx = LENGTH last.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `st.cs_next_var <= last.cs_next_var` by
   (drule abi_decoder_variable_counter >> simp[]) >>
 `fresh_vars_wrt last initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 `ctor_actual_scratch func (frag_ids st last) 0 initial.vs_alloca_next initial` by
   (simp_tac bool_ss [ctor_actual_scratch_def, frag_ids_def, GSPECIFICATION] >>
    rpt strip_tac >> res_tac >> gvs[]) >>
 drule (BETA_RULE prefix_canonical_coherent_complete_code) >>
 disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `eval_operand (Var dst) initial = _`)) >>
 disch_then (drule_at (Pat `fresh_vars_wrt last initial`)) >>
 simp_tac bool_ss [LESS_EQ_REFL, SUBSET_REFL] >>
 disch_then (qspecl_then [`k`,`ctx`,`func`,`site`,`sb`] mp_tac) >>
 disch_then (qspecl_then [`0`,`initial.vs_alloca_next`,`frag_ids st last`] mp_tac) >>
 simp_tac bool_ss [ADD, ZERO_LESS_EQ, SUBSET_REFL, LESS_EQ_REFL] >>
 disch_then drule_all >>
 disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
 qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[] >>
 metis_tac[]
QED

Theorem prefix_entry_register_scratch_extend[local]:
 abi_encoder_registered_effect (ctor_actual_sites func child) outs s t /\
 ctor_actual_scratch func child d n t /\
 (!i. i IN full /\ i NOTIN child ==> FLOOKUP s.vs_allocas i = NONE) ==>
 ctor_actual_scratch func full d n t
Proof
 simp_tac bool_ss [ctor_actual_scratch_def, abi_encoder_registered_effect_def] >>
 strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `inst.inst_id IN child`
 >- metis_tac[] >>
 `inst.inst_id NOTIN ctor_actual_sites func child` by simp[ctor_actual_sites_def] >>
 metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem prefix_entry_register_address_decode_paired:
 !ptr. i < LENGTH atys /\ LENGTH avs = LENGTH atys /\
 EL i atys = vyper_to_abi_type env ty /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 LENGTH encoded < dimword (:256) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) v /\
 FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
 lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
   DLOAD (Lit 0w) 0 st = ((),last) /\
 fresh_vars_wrt st initial /\ fn_has_code st last func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = last.cs_blocks \/ !bb.
   lookup_block last.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 FLOOKUP G ptr = SOME (b,sz) /\ b <= d /\ d + type_memory_bytes ce ty <= b+sz /\
 op_taint tn (Var ptr) = {} /\
 allocas_from lo initial /\ ~ctx_has_dalloca ctx /\ lo <= initial.vs_alloca_next /\ lo <= d /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual H qt B.
 allocas_from lo actual /\ lo <= actual.vs_alloca_next /\
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st last))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st last) 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt last actual /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = last.cs_current_bb /\
 actual.vs_inst_idx = LENGTH last.cs_current_insts /\ abi_decode_sim ctx func initial actual /\
 actual.vs_code = initial.vs_code /\ actual.vs_outcomes = initial.vs_outcomes /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx /\
 actual.vs_gas_readings = initial.vs_gas_readings /\
 (!a. a < lo ==> read_byte a actual.vs_memory = read_byte a initial.vs_memory) /\
 FINITE B /\ B SUBSET range_bytes [(d,type_memory_bytes ce ty)] /\ DISJOINT B qt.t_mem /\
 (!mem. (!a. a IN B ==> mem_bytes_at a 1 mem = mem_bytes_at a 1 actual.vs_memory) ==>
   val_in_memory tv v d mem) /\
 qt.t_mem SUBSET tn.t_mem /\
 qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
 (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
   op_taint qt (Var x) = op_taint tn (Var x)) /\
 ((!fuel. ptr_safe_run D lo fuel ctx func PG H qt actual) ==>
   !fuel. ptr_safe_run D lo fuel ctx func PG G tn initial)
Proof
 gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all prefix_entry_register_canonical_address_paired >>
 disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] mp_tac) >>
 disch_then (qx_choose_then `src` (qx_choose_then `middle`
   (qx_choose_then `prepared` (qx_choose_then `sb` (qx_choose_then `AG`
     (qx_choose_then `atn` (map_every assume_tac o CONJUNCTS))))))) >>
 `middle.cs_current_bb = st.cs_current_bb` by
   (qpat_x_assum `cs_extends st middle` mp_tac >> simp[cs_extends_def]) >>
 `alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared` by
   (asm_rewrite_tac[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def] >>
    metis_tac[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
       alloca_frontier_inv_from_def, remaining_alloca_budget_def]) >>
 `!aid. middle.cs_next_id <= aid ==> FLOOKUP prepared.vs_allocas aid = NONE` by
   (rpt strip_tac >> simp[] >> first_x_assum irule >> decide_tac) >>
 `FLOOKUP AG ptr' = SOME (b,sz) /\ op_taint atn (Var ptr') = {}` by metis_tac[] >>
 `d + type_memory_bytes ce ty <= prepared.vs_alloca_next /\
  lo <= prepared.vs_alloca_next` by simp[] >>
 drule_all prefix_entry_register_decode_paired >>
 disch_then (qspecl_then [`PG`,`D`] mp_tac) >>
 disch_then (qx_choose_then `actual` (qx_choose_then `H` (qx_choose_then `qt`
   (qx_choose_then `B` (map_every assume_tac o CONJUNCTS))))) >>
 `!x. not_fresh_at st x ==> not_fresh_at middle x` by
   (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 qexistsl [`actual`,`H`,`qt`,`B`] >> asm_rewrite_tac[] >>
 conj_tac >- suspend "effect" >>
 conj_tac >- suspend "scratch" >>
 metis_tac[abi_decode_sim_trans]
QED

Resume prefix_entry_register_address_decode_paired[effect]:
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle last))
   [(d,type_memory_bytes ce ty)] initial prepared` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`{}`,`[]`] >> simp[]) >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle last))
   [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_trans >> qexists `prepared` >> simp[]) >>
 irule abi_encoder_registered_effect_enlarge >>
 goal_assum (drule_at Any) >> simp[ctor_actual_sites_def, SUBSET_DEF] >> metis_tac[SUBSET_DEF]
QED

Resume prefix_entry_register_address_decode_paired[scratch]:
 `ctor_actual_scratch func (frag_ids middle last) 0 initial.vs_alloca_next actual` by
   metis_tac[] >>
 irule prefix_entry_register_scratch_extend >>
 qexistsl [`frag_ids middle last`,`[(d,type_memory_bytes ce ty)]`,`prepared`] >>
 asm_rewrite_tac[] >> simp[frag_ids_def] >> rpt strip_tac >>
 simp[] >> qpat_x_assum `!aid. st.cs_next_id <= aid ==> _` irule >> simp[]
QED

Finalise prefix_entry_register_address_decode_paired

val _ = export_theory();
