Theory ctorDeployMemoryRunMemEntryCheckedArgWorld
Ancestors
  loweringStateRelDefs
  ctorDeployLoweringEntryAddress
 ctorDeployMemoryRunMemEntryShiftedRegistration
 ctorDeployMemoryRunMemEntryCheckedRecursiveWorld
 ctorDeployMemoryRunMemEntrySequenceWorld
 ctorDeployMemoryRunMemEntryRegistration ctorArgDecode ctorRegisterArgs
 ctorDeployMemoryRunMemEntryShiftedAlloc ctorDeployMemoryRunMemEntryShiftedFrame
 ctorDeployMemoryFrontier
 abiDecoderMemberBody abiDecoderMemberSlice abiDecoderTypedContract abiDecoderCoherence
 abiDecoderContract abiEncoderProps valueEncoding contractABI vyperABI
 abiDecoderReentryAddress abiDecoderReentry ctorAbiActualMemory
 actualAllocCredit actualAllocExec allocaHistory loweringHalt
 ctorDeployMemoryRunMemEntryArraySteps venomExecSemantics
 abiDecoderCounters exprLoweringProps ctorAbiActualSites abiDecoderCode
 abiEncoderRegisteredEffect emitHelperProps ctorAbiActualFrame
 ctorDeployMemoryRunMemEntryCompositeSetup fragExecMem emitHelper context
 fragExec abiDecoderAppend instIdxIndep abiDecoderLoop
 instMemFrontier unitTransformDefs memSafeRun abiDecodeRanges
 ctorDeployMemoryRunMemEntryCheckedStep venomMemDefs allocaFrontierBound
 moduleLowering abiEncoder compileVyper localPtrsProps entryArgPtrs fragGasPathMem
 words list rich_list finite_map pred_set arithmetic exprLowering compileEnv venomInst venomState

(* Common result of decoding a single argument, with its actual world frame. *)
val Aw = ``\r ce ty tv v st st' ctx func site initial d actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv_from r ctx func site actual /\
 d + type_memory_bytes ce ty <= actual.vs_alloca_next /\
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
 actual.vs_outcomes = initial.vs_outcomes``;

Theorem ctor_checked_arg_decoder_world_actual_from:
 !r dst src hi ce env ty tv av v st st' ctx func site initial sb d.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),st') /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\
 alloca_history func initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. (^Aw) r ce ty tv v st st' ctx func site initial d actual
Proof
 rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `st.cs_next_var <= st'.cs_next_var` by
   (drule abi_decoder_variable_counter >> simp[]) >>
 `fresh_vars_wrt st' initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 `ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next initial` by
   (simp_tac bool_ss [ctor_actual_scratch_def, frag_ids_def, GSPECIFICATION] >>
    rpt strip_tac >> res_tac >> gvs[]) >>
 drule (BETA_RULE ctor_checked_coherent_world_run_from) >>
 disch_then (drule_at Any) >>
 disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `eval_operand dst initial = _`)) >>
 disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
 simp_tac bool_ss [LESS_EQ_REFL, SUBSET_REFL] >>
 disch_then (qspecl_then [`r`, `ctx`, `site`, `d`] mp_tac) >>
 simp_tac bool_ss [ADD, ZERO_LESS_EQ, LESS_EQ_REFL] >>
 disch_then drule_all >> strip_tac >>
 `abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_enlarge >>
    goal_assum (drule_at Any) >> simp[ctor_actual_sites_subset]) >>
 BETA_TAC >> qexists `actual` >> asm_rewrite_tac[] >>
 fs[abi_encoder_registered_effect_def, frag_ids_def] >>
 rpt strip_tac >>
 `st.cs_next_id <= st'.cs_next_id` by
   (drule abi_decoder_to_buf_code >> simp[abi_decode_source_opcode_def, abi_decoder_code_def]) >>
 metis_tac[LESS_EQ_TRANS, NOT_LESS_EQUAL]
QED

Theorem ctor_world_scratch_extend[local]:
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

Theorem ctor_world_setup_effect_transport[local]:
 abi_encoder_registered_effect {} [] initial prepared /\
 prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle st')) outs prepared actual /\
 ctor_actual_scratch func (frag_ids middle st') 0 prepared.vs_alloca_next actual /\
 st.cs_next_id <= middle.cs_next_id /\ middle.cs_next_id <= st'.cs_next_id /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) ==>
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) outs initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual
Proof
 strip_tac >>
 `frag_ids middle st' SUBSET frag_ids st st'` by
   (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle st')) outs initial prepared` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`{}:num set`, `[]:(num#num) list`] >> simp[EVERY_DEF]) >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle st')) outs initial actual` by
   metis_tac[abi_encoder_registered_effect_trans] >>
 conj_tac
 >- (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`ctor_actual_sites func (frag_ids middle st')`, `outs`] >>
     simp[ctor_actual_sites_mono]) >>
 irule ctor_world_scratch_extend >>
 qexistsl [`frag_ids middle st'`, `outs`, `initial`] >> simp[] >>
 rpt strip_tac >> fs[frag_ids_def] >> metis_tac[]
QED

Theorem ctor_checked_arg_setup_decode_world_actual_from:
 !r pvar sb st src middle ce ty data_size st' env tv av v initial prepared d func ctx site.
 cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
 st.cs_next_id <= middle.cs_next_id /\ st.cs_next_var <= middle.cs_next_var /\
 abi_decode_sim ctx func initial prepared /\
 gas_path_mem ctx func initial 0 (OK prepared) /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared /\
 prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx /\
 prepared.vs_outcomes = initial.vs_outcomes /\
 eval_operand src prepared = SOME (n2w sb) /\
 abi_decoder_operand_live middle.cs_next_var src /\
 fresh_vars_wrt middle prepared /\ alloca_inv prepared /\
 alloca_frontier_inv_from r ctx func site prepared /\
 prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x prepared = SOME w) /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 compile_abi_decode_to_buf (Var pvar) src DLOAD (Lit 0w) (Lit (n2w data_size))
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),st') /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
 lookup_var pvar initial = SOME (n2w d) /\ not_fresh_at st pvar /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (data_size = 0 \/ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= data_size /\
   data_size < dimword (:256)) /\
 fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 r + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) ==>
 ?actual. (^Aw) r ce ty tv v st st' ctx func site initial d actual
Proof
 rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `eval_operand (Var pvar) prepared = SOME (n2w d)` by
   (simp[eval_operand_def] >> first_x_assum irule >> asm_rewrite_tac[]) >>
 `!x. src = Var x \/ Var pvar = Var x \/ Lit (n2w data_size) = Var x ==>
   not_fresh_at middle x` by
   (qpat_x_assum `abi_decoder_operand_live _ src` mp_tac >>
    qpat_x_assum `not_fresh_at st pvar` mp_tac >>
    qpat_x_assum `st.cs_next_var <= middle.cs_next_var` mp_tac >>
    rpt (pop_assum kall_tac) >> Cases_on `src` >>
    simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
    metis_tac[LESS_EQ_TRANS]) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `st.cs_blocks = middle.cs_blocks` by asm_rewrite_tac[] >>
 drule cs_extends_abi_decode >> strip_tac >>
 drule_all fn_has_code_split >> strip_tac >>
 drule abi_decoder_variable_counter >> strip_tac >>
 drule_all abi_decoder_to_buf_code >>
 simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
 qpat_x_assum `!i. abi_decoder_code_member _ _ ==> _` kall_tac >>
 `frag_ids middle st' SUBSET frag_ids st st'` by
   (qpat_x_assum `st.cs_next_id <= middle.cs_next_id` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
 Q.SUBGOAL_THEN
   `middle.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` assume_tac >- metis_tac[] >>
 `!aid. middle.cs_next_id <= aid ==> FLOOKUP prepared.vs_allocas aid = NONE` by
   (asm_rewrite_tac[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 qpat_assum `eval_operand src prepared = _` assume_tac >>
 drule (BETA_RULE ctor_checked_arg_decoder_world_actual_from) >>
 disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `eval_operand src prepared = _`)) >>
 disch_then (qspecl_then [`r`, `ctx`, `func`, `site`, `d`] mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >>
   Cases_on `data_size = 0` >> fs[eval_operand_def] >>
   qexists `data_size` >> fs[eval_operand_def])) >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial prepared` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`{}`, `[]`] >> asm_rewrite_tac[EMPTY_SUBSET, EVERY_DEF]) >>
 `abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] prepared actual` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`frag_ids middle st'`, `[(d,type_memory_bytes ce ty)]`] >>
    asm_rewrite_tac[]) >>
 `abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_trans >> qexists `prepared` >> asm_rewrite_tac[]) >>
 drule_all ctor_world_setup_effect_transport >> strip_tac >>
 `initial.vs_alloca_next <= actual.vs_alloca_next` by metis_tac[] >>
 `abi_decode_sim ctx func initial actual` by
   (irule abi_decode_sim_trans >> qexists `prepared` >> asm_rewrite_tac[]) >>
 `gas_path_mem ctx func initial 0 (OK actual)` by
   metis_tac[ctor_checked_path_append, ADD_0] >>
 BETA_TAC >> qexists `actual` >> asm_rewrite_tac[] >>
 rpt gen_tac >> strip_tac >>
 `not_fresh_at middle x` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 metis_tac[]
QED

Theorem ctor_checked_arg_add_decode_world_actual_from:
 !r ptr sb st src middle ce ty data_size st' env tv av v initial d func ctx site.
 emit_op ADD [Lit 0w; Lit (n2w sb)] st = (src,middle) /\
 compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit (n2w data_size))
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),st') /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
 lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (data_size = 0 \/ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= data_size /\
   data_size < dimword (:256)) /\
 fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\
 alloca_history func initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. (^Aw) r ce ty tv v st st' ctx func site initial d actual
Proof
 rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 rename1 `lookup_var pvar initial = SOME (n2w d)` >>
 drule ctor_checked_arg_emit_shape >> strip_tac >>
 `st.cs_blocks = middle.cs_blocks` by simp[] >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `st.cs_next_id <= middle.cs_next_id` by simp[] >>
 drule cs_extends_abi_decode >> strip_tac >>
 drule_all fn_has_code_split >> strip_tac >>
 drule abi_decoder_variable_counter >> strip_tac >>
 drule_all abi_decoder_to_buf_code >>
 simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
 qpat_x_assum `!i. abi_decoder_code_member _ _ ==> _` kall_tac >>
 `frag_ids middle st' SUBSET frag_ids st st'` by
   (qpat_x_assum `st.cs_next_id <= middle.cs_next_id` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
 Q.SUBGOAL_THEN
   `middle.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` assume_tac >- metis_tac[] >>
 drule ctor_checked_arg_add_reach >> simp_tac (srw_ss()) [eval_operand_def] >>
 disch_then drule_all >>
 disch_then (qspec_then `ctx` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func initial prepared` >>
 `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x prepared = SOME w` by
   (rpt strip_tac >>
    qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _`
      (qspec_then `Var x` mp_tac) >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, eval_operand_def, Abbr `prepared`, lookup_var_def]) >>
 `eval_operand src prepared = SOME (n2w sb)` by
   fs[Abbr `prepared`, eval_op_inst_idx] >>
 `abi_decoder_operand_live middle.cs_next_var src` by
   (irule abi_decoder_operand_live_fresh >> goal_assum (drule_at Any) >>
    goal_assum (drule_at Any)) >>
 `sb < dimword (:256)` by decide_tac >>
 qpat_x_assum `st.cs_blocks = middle.cs_blocks` kall_tac >>
 BETA_TAC >> irule (BETA_RULE ctor_checked_arg_setup_decode_world_actual_from) >> asm_simp_tac bool_ss [] >>
 goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `abi_decode_sim _ _ _ _`)) >>
 qexistsl [`av`, `env`, `sb`] >>
 qpat_x_assum `st.cs_current_bb = middle.cs_current_bb` kall_tac >>
 `alloca_frontier_inv_from r ctx func site prepared` by
   (irule alloca_frontier_inv_from_frame >> goal_assum (drule_at Any) >>
    simp[Abbr `prepared`, update_var_def]) >>
 simp[Abbr `prepared`, ctor_checked_arg_register_observations,
      abi_encoder_registered_effect_def, update_var_def] >>
 Cases_on `data_size = 0` >> fs[]
QED

Theorem ctor_checked_arg_dynamic_world_setup:
 emit_op ADD [Lit 0w; Lit (n2w off)] st = (head,m1) /\
 emit_op DLOAD [head] m1 = (rel,m2) /\
 emit_op ADD [Lit 0w; rel] m2 = (src,middle) /\
 off < dimword (:256) /\ off + 32 <= LENGTH initial.vs_data_section /\
 abi_decode_load DLOAD (n2w off : bytes32) initial = n2w sb /\
 fresh_vars_wrt st initial /\ alloca_history func initial /\
 fn_has_code st m1 func /\ fn_has_code m1 m2 func /\ fn_has_code m2 middle func /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared.
 eval_operand src prepared = SOME (n2w sb) /\
 fresh_vars_wrt middle prepared /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x prepared = SOME w) /\
 prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 alloca_inv prepared = alloca_inv initial /\
 alloca_frontier_inv ctx func site prepared = alloca_frontier_inv ctx func site initial /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 abi_decode_sim ctx func initial prepared /\
 gas_path_mem ctx func initial 0 (OK prepared) /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared /\
 prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx /\
 prepared.vs_outcomes = initial.vs_outcomes
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 qpat_assum `emit_op ADD [Lit 0w; Lit (n2w off)] st = _`
   (mp_then Any mp_tac ctor_checked_arg_add_reach) >>
 simp_tac (srw_ss()) [eval_operand_def] >> disch_then drule_all >>
 disch_then (qspec_then `ctx` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qmatch_asmsub_abbrev_tac `abi_decode_sim ctx func initial s1` >>
 `eval_operand head s1 = SOME (n2w off) /\ ~s1.vs_halted /\
  s1.vs_current_bb = m1.cs_current_bb /\ s1.vs_inst_idx = LENGTH m1.cs_current_insts /\
  off + 32 <= LENGTH s1.vs_data_section` by
   fs[Abbr `s1`, update_var_def] >>
 drule ctor_checked_arg_read_reach >> disch_then drule_all >>
 disch_then (qspec_then `ctx` (qx_choose_then `s2` (MAP_EVERY assume_tac o CONJUNCTS))) >>
 `abi_decode_load DLOAD (n2w off : bytes32) s1 = n2w sb` by
   gvs[abi_decode_load_def, abi_decode_source_def, Abbr `s1`, update_var_def,
       w2n_n2w] >>
 `eval_operand rel s2 = SOME (n2w sb) /\ s2.vs_inst_idx = LENGTH m2.cs_current_insts` by
   (conj_tac >- (qpat_assum `eval_operand rel s2 = _` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
    qpat_x_assum `s2 = _` (fn th => simp[th])) >>
 `eval_operand (Lit 0w) s2 = SOME 0w` by simp[eval_operand_def] >>
 qpat_assum `emit_op ADD [Lit 0w; rel] m2 = _`
   (mp_then Any mp_tac ctor_checked_arg_add_reach) >>
 disch_then drule_all >>
 disch_then (qspec_then `ctx` (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS))) >>
 `st.cs_next_var <= m1.cs_next_var /\ st.cs_next_var <= m2.cs_next_var` by
   (imp_res_tac ctor_checked_arg_emit_shape >> decide_tac) >>
 `!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x prepared = SOME w` by
   (rpt strip_tac >>
    `abi_decoder_operand_live st.cs_next_var (Var x) /\
     abi_decoder_operand_live m1.cs_next_var (Var x) /\
     abi_decoder_operand_live m2.cs_next_var (Var x)` by
      (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
       metis_tac[LESS_EQ_TRANS]) >>
    qpat_x_assum `!op. abi_decoder_operand_live m2.cs_next_var op ==> _`
      (qspec_then `Var x` mp_tac) >>
    qpat_x_assum `!op. abi_decoder_operand_live m1.cs_next_var op ==> _`
      (qspec_then `Var x` mp_tac) >>
    qpat_x_assum `!op. abi_decoder_operand_live st.cs_next_var op ==> _`
      (qspec_then `Var x` mp_tac) >>
    asm_rewrite_tac[eval_operand_def] >>
    fs[Abbr `s1`, lookup_var_def] >> metis_tac[]) >>
 `abi_decode_sim ctx func initial prepared` by metis_tac[abi_decode_sim_trans] >>
 `gas_path_mem ctx func initial 0 (OK s2)` by
   metis_tac[ctor_checked_path_append, ADD_0] >>
 `gas_path_mem ctx func initial 0 (OK prepared)` by
   metis_tac[ctor_checked_path_append, ADD_0] >>
 qexists `prepared` >> asm_rewrite_tac[] >>
 qpat_x_assum `prepared = _` (fn th => rewrite_tac[th]) >>
 qpat_x_assum `s2 = _` (fn th => rewrite_tac[th]) >>
 simp[Abbr `s1`, ctor_checked_arg_register_observations, alloca_frontier_inv_def,
      abi_encoder_registered_effect_def, update_var_def]
QED

Theorem ctor_checked_arg_dynamic_decode_world_actual_from:
 !r pvar sb off st head m1 rel m2 src middle ce ty data_size st' env tv av v initial d func ctx site.
 emit_op ADD [Lit 0w; Lit (n2w off)] st = (head,m1) /\
 emit_op DLOAD [head] m1 = (rel,m2) /\
 emit_op ADD [Lit 0w; rel] m2 = (src,middle) /\
 off < dimword (:256) /\ off + 32 <= LENGTH initial.vs_data_section /\
 abi_decode_load DLOAD (n2w off : bytes32) initial = n2w sb /\
 compile_abi_decode_to_buf (Var pvar) src DLOAD (Lit 0w) (Lit (n2w data_size))
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) middle = ((),st') /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
 lookup_var pvar initial = SOME (n2w d) /\ not_fresh_at st pvar /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (data_size = 0 \/ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= data_size /\
   data_size < dimword (:256)) /\
 fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\
 alloca_history func initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. (^Aw) r ce ty tv v st st' ctx func site initial d actual
Proof
 rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `cs_extends st m1 /\ cs_extends m1 m2 /\ cs_extends m2 middle /\
  m1.cs_blocks = st.cs_blocks /\ m2.cs_blocks = st.cs_blocks /\
  middle.cs_blocks = st.cs_blocks /\
  st.cs_next_id <= middle.cs_next_id /\ st.cs_next_var <= middle.cs_next_var` by
   (imp_res_tac ctor_checked_arg_emit_shape >> simp[] >> decide_tac) >>
 `cs_extends st m2 /\ cs_extends st middle` by metis_tac[cs_extends_trans] >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule cs_extends_abi_decode >> strip_tac >>
 drule_all fn_has_code_split >> strip_tac >>
 drule abi_decoder_variable_counter >> strip_tac >>
 drule_all abi_decoder_to_buf_code >>
 simp_tac bool_ss [abi_decoder_code_def] >> strip_tac >>
 qpat_x_assum `!i. abi_decoder_code_member _ _ ==> _` kall_tac >>
 `frag_ids middle st' SUBSET frag_ids st st'` by
   (qpat_x_assum `st.cs_next_id <= middle.cs_next_id` mp_tac >>
    POP_ASSUM_LIST (K ALL_TAC) >>
    simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
 Q.SUBGOAL_THEN
   `middle.cs_blocks = st'.cs_blocks \/
    !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0` assume_tac >- metis_tac[] >>
 `fn_has_code st m1 func /\ fn_has_code m1 m2 func /\ fn_has_code m2 middle func` by
   metis_tac[fn_has_code_split, cs_extends_trans] >>
 drule_all ctor_checked_arg_dynamic_world_setup >>
 disch_then (qspecl_then [`site`, `ctx`]
   (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS))) >>
 `alloca_frontier_inv_from r ctx func site prepared` by
   (irule alloca_frontier_inv_from_frame >>
    goal_assum (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >> simp[]) >>
 `abi_decoder_operand_live middle.cs_next_var src` by
   (irule abi_decoder_operand_live_fresh >> goal_assum (drule_at Any) >>
    goal_assum (drule_at Any)) >>
 BETA_TAC >> irule (BETA_RULE ctor_checked_arg_setup_decode_world_actual_from) >> asm_simp_tac bool_ss [] >>
 goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `abi_decode_sim _ _ initial prepared`)) >>
 asm_rewrite_tac[] >>
 qexistsl [`av`, `env`, `sb`] >> simp[]
QED

Theorem ctor_world_arg_static_code[local]:
 !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var (ptr:string)) (type_memory_bytes ce ty)) /\
 ~is_abi_dynamic ce.ce_struct_fields ty ==>
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
     DLOAD (Lit (n2w data_size)) 0 =
 do src <- emit_op ADD [Lit 0w; Lit (n2w off)];
    compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit (n2w data_size))
      (type_to_abi_dec_info ce.ce_struct_fields ce ty)
 od
Proof
 rpt strip_tac >> Cases_on `is_word_type ty`
 >- (`?clamp. type_to_abi_dec_info ce.ce_struct_fields ce ty = DecPrimWord clamp` by
      (Cases_on `ty` >> fs[is_word_type_def, type_to_abi_dec_info_def] >>
       rename1 `BaseT bt` >> Cases_on `bt` >>
       fs[is_word_type_def, type_to_abi_dec_info_def] >>
       rename1 `BytesT b` >> Cases_on `b` >>
       fs[is_word_type_def, type_to_abi_dec_info_def]) >>
     simp[build_positional_arg_def, compile_decode_args_def,
          var_location_decode_operand_def, compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
          compile_abi_decode_static_def, FUN_EQ_THM,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[]) >>
 simp[build_positional_arg_def, compile_decode_args_def,
      var_location_decode_operand_def, FUN_EQ_THM,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
 rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ctor_world_arg_dynamic_code[local]:
 !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
 ~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty ==>
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
     DLOAD (Lit (n2w data_size)) 0 =
 do static_src <- emit_op ADD [Lit 0w; Lit (n2w off)];
    offset_val <- emit_op DLOAD [static_src];
    src <- emit_op ADD [Lit 0w; offset_val];
    compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit 0w) (Lit (n2w data_size))
      (type_to_abi_dec_info ce.ce_struct_fields ce ty)
 od
Proof
 rpt strip_tac >>
 simp[build_positional_arg_def, compile_decode_args_def,
      var_location_decode_operand_def, FUN_EQ_THM,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
 rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
 pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ctor_world_selected_type[local]:
 i < LENGTH fargs /\ EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) ==>
 LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env ty
Proof
 `!tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys` by
   (Induct >> simp[vyper_to_abi_type_def]) >>
 simp[MAP_COMPOSE, EL_MAP]
QED

Theorem ctor_checked_decode_constructor_arg_world_from:
 !r ce env fargs avs atys encoded i name ty tv v off data_size
  ptr d st st' ctx func site initial.
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\ EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\ LENGTH encoded <= LENGTH initial.vs_data_section /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
   DLOAD (Lit (n2w data_size)) 0 st = ((),st') /\
 FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
 lookup_var ptr initial = SOME (n2w d) /\ not_fresh_at st ptr /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) v /\
 fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from r ctx func site initial /\
 alloca_history func initial /\ r + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. (^Aw) r ce ty tv v st st' ctx func site initial d actual
Proof
 BETA_TAC >> rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all ctor_checked_arg_member_source >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 rename1 `lookup_var pvar initial = SOME (n2w d)` >>
 `data_size <> 0 ==> abi_tuple_child_offset atys avs i +
    LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= data_size /\
    data_size < dimword (:256)` by metis_tac[LESS_EQ_TRANS] >>
 Cases_on `is_abi_dynamic ce.ce_struct_fields ty`
 >- (`~is_word_type ty` by
       (Cases_on `ty` >> fs[is_word_type_def, is_abi_dynamic_def] >>
        rename1 `BaseT bt` >> Cases_on `bt` >> fs[is_word_type_def, is_abi_dynamic_def] >>
        rename1 `BytesT b` >> Cases_on `b` >> fs[is_word_type_def, is_abi_dynamic_def]) >>
     `is_dynamic (EL i atys)` by
       (drule abi_decoder_coherent_header >>
        simp[abi_decoder_header_def] >> strip_tac >>
        drule_all ctor_world_selected_type >> simp[]) >>
     `off + 32 <= LENGTH initial.vs_data_section /\ off < dimword (:256)` by
       (drule_all ctor_world_selected_type >> strip_tac >>
        irule ctor_checked_arg_dynamic_head_section >>
        qexistsl [`atys`, `avs`, `i`] >> gvs[Excl "enc_def"]) >>
     drule_all ctor_world_arg_dynamic_code >> strip_tac >>
     qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
     pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
     pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
     pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
     irule (BETA_RULE ctor_checked_arg_dynamic_decode_world_actual_from) >> asm_rewrite_tac[] >>
     goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [Lit 0w; _] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op DLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     asm_rewrite_tac[] >> qexistsl [`EL i avs`, `env`, `abi_tuple_child_offset atys avs i`] >>
     gvs[Excl "enc_def"]) >>
 drule_all ctor_world_arg_static_code >> strip_tac >>
 qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
 asm_rewrite_tac[] >> simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
 pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
 irule (BETA_RULE ctor_checked_arg_add_decode_world_actual_from) >> asm_rewrite_tac[] >>
 goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
 asm_rewrite_tac[] >> qexistsl [`EL i avs`, `env`] >> gvs[Excl "enc_def"]
QED
