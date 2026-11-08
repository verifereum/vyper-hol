Theory ctorDeployMemoryRunMemEntryRegistration
Ancestors
  loweringStateRelDefs
  ctorDeployLoweringEntryAddress ctorDeployLoweringEntryRegisterRun
 ctorDeployMemoryRunMemEntryRecursive ctorArgDecode ctorRegisterArgs
 abiDecoderMemberBody abiDecoderMemberSlice abiDecoderTypedContract abiDecoderCoherence
 abiDecoderContract abiEncoderProps valueEncoding contractABI vyperABI
 abiDecoderReentryAddress abiDecoderReentry ctorAbiActualMemory
 actualAllocCredit actualAllocExec allocaHistory loweringHalt
 ctorDeployMemoryRunMemEntryArraySteps venomExecSemantics
 abiDecoderCounters exprLoweringProps ctorAbiActualSites abiDecoderCode
 abiEncoderRegisteredEffect emitHelperProps ctorAbiActualFrame
 ctorDeployMemoryRunMemEntryCompositeSetup fragExecMem emitHelper context
 fragExec abiDecoderAppend abiDecoderReentry instIdxIndep abiDecoderLoop
 instMemFrontier unitTransformDefs memSafeRun abiDecodeRanges
 ctorDeployMemoryRunMemEntryCheckedStep venomMemDefs allocaFrontierBound
 moduleLowering abiEncoder compileVyper localPtrsProps entryArgPtrs fragGasPathMem
 words list rich_list finite_map pred_set arithmetic exprLowering compileEnv venomInst venomState

Theorem ctor_checked_selected_type[local]:
 i < LENGTH fargs /\ EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) ==>
 LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env ty
Proof
 `!tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys` by
   (Induct >> simp[vyper_to_abi_type_def]) >>
 simp[MAP_COMPOSE, EL_MAP]
QED

Theorem ctor_checked_tuple_member[local]:
 i < LENGTH atys /\ LENGTH avs = LENGTH atys /\ has_types atys avs /\
 mem_bytes_at 0 (LENGTH (enc (Tuple atys) (ListV avs)))
   (abi_decode_source DLOAD initial) = enc (Tuple atys) (ListV avs) /\
 LENGTH (enc (Tuple atys) (ListV avs)) < dimword (:256) ==>
 has_type (EL i atys) (EL i avs) /\
 mem_bytes_at (abi_tuple_child_offset atys avs i)
   (LENGTH (enc (EL i atys) (EL i avs))) (abi_decode_source DLOAD initial) =
     enc (EL i atys) (EL i avs) /\
 abi_tuple_child_offset atys avs i + LENGTH (enc (EL i atys) (EL i avs)) <=
   LENGTH (enc (Tuple atys) (ListV avs)) /\
 (is_dynamic (EL i atys) ==>
   abi_decode_load DLOAD (n2w (SUM (MAP abi_member_head_size (TAKE i atys))) : bytes32) initial =
     n2w (abi_tuple_child_offset atys avs i) /\
   abi_tuple_child_offset atys avs i < dimword (:256)) /\
 (~is_dynamic (EL i atys) ==>
   abi_tuple_child_offset atys avs i = SUM (MAP abi_member_head_size (TAKE i atys)))
Proof
 strip_tac >>
 `TAKE i atys ++ EL i atys::DROP (SUC i) atys = atys` by
   (mp_tac (Q.ISPEC `atys:abi_type list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
    asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
 `TAKE i avs ++ EL i avs::DROP (SUC i) avs = avs` by
   (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
    asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
 `LENGTH (TAKE i atys) = i /\ LENGTH (TAKE i avs) = i` by simp[] >>
 mp_tac (Q.INST [`pre` |-> `TAKE i atys`, `ty` |-> `EL i atys`,
   `post` |-> `DROP (SUC i) atys`, `pvs` |-> `TAKE i avs`,
   `v` |-> `EL i avs`, `rest` |-> `DROP (SUC i) avs`,
   `sb` |-> `0`, `opc` |-> `DLOAD`, `s` |-> `initial`]
   abi_tuple_child_offset_source) >>
 asm_simp_tac bool_ss [ADD_CLAUSES] >> strip_tac >>
 mp_tac (Q.INST [`pre` |-> `TAKE i atys`, `ty` |-> `EL i atys`,
   `post` |-> `DROP (SUC i) atys`, `pvs` |-> `TAKE i avs`,
   `v` |-> `EL i avs`, `rest` |-> `DROP (SUC i) avs`]
   abi_tuple_child_offset_ranges) >>
 asm_simp_tac bool_ss [] >> strip_tac >>
 mp_tac (Q.INST [`pre` |-> `TAKE i atys`, `aty` |-> `EL i atys`,
   `post` |-> `DROP (SUC i) atys`, `pvs` |-> `TAKE i avs`,
   `av` |-> `EL i avs`, `avs` |-> `DROP (SUC i) avs`,
   `sb` |-> `0`, `opc` |-> `DLOAD`, `s` |-> `initial`]
   abi_decoder_canonical_member_inputs) >>
 asm_simp_tac bool_ss [ADD_CLAUSES] >>
 Cases_on `is_dynamic (EL i atys)` >> simp[] >> strip_tac >> gvs[]
QED

Theorem ctor_checked_arg_member_source:
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\
 LENGTH encoded <= LENGTH initial.vs_data_section /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv ==>
 has_type (vyper_to_abi_type env ty) (EL i avs) /\
 mem_bytes_at (abi_tuple_child_offset atys avs i)
   (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))) initial.vs_data_section =
     enc (vyper_to_abi_type env ty) (EL i avs) /\
 abi_tuple_child_offset atys avs i +
   LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= LENGTH encoded /\
 abi_tuple_child_offset atys avs i +
   LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) < dimword (:256) /\
 abi_tuple_child_offset atys avs i +
   LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= LENGTH initial.vs_data_section /\
 (is_abi_dynamic ce.ce_struct_fields ty ==>
   abi_decode_load DLOAD (n2w off : bytes32) initial =
     n2w (abi_tuple_child_offset atys avs i)) /\
 (~is_abi_dynamic ce.ce_struct_fields ty ==>
   abi_tuple_child_offset atys avs i = off)
Proof
 strip_tac >>
 drule_all ctor_checked_selected_type >> strip_tac >>
 drule abi_decoder_coherent_header >>
 simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
 `i < LENGTH atys /\ LENGTH avs = LENGTH atys` by simp[] >>
 `mem_bytes_at 0 (LENGTH (enc (Tuple atys) (ListV avs)))
     (abi_decode_source DLOAD initial) = enc (Tuple atys) (ListV avs)` by
   gvs[abi_decode_source_def, Excl "enc_def"] >>
 `LENGTH (enc (Tuple atys) (ListV avs)) < dimword (:256)` by metis_tac[] >>
 drule_all ctor_checked_tuple_member >>
 gvs[abi_decode_source_def, Excl "enc_def"]
QED

Theorem ctor_checked_arg_decoder_actual:
 !dst src hi ce env ty tv av v st st' ctx func site initial sb d.
 compile_abi_decode_to_buf dst src DLOAD hi
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
 rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `st.cs_next_var <= st'.cs_next_var` by
   (drule abi_decoder_variable_counter >> simp[]) >>
 `fresh_vars_wrt st' initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 `ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next initial` by
   (simp_tac bool_ss [ctor_actual_scratch_def, frag_ids_def, GSPECIFICATION] >>
    rpt strip_tac >> res_tac >> gvs[]) >>
 drule (BETA_RULE ctor_checked_coherent_run) >>
 disch_then (drule_at Any) >>
 disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `eval_operand dst initial = _`)) >>
 disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
 simp_tac bool_ss [LESS_EQ_REFL, SUBSET_REFL] >>
 disch_then (qspecl_then [`ctx`, `site`, `d`] mp_tac) >>
 simp_tac bool_ss [ADD, ZERO_LESS_EQ, LESS_EQ_REFL] >>
 disch_then drule_all >> strip_tac >>
 `abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_enlarge >>
    goal_assum (drule_at Any) >> simp[ctor_actual_sites_subset]) >>
 qexists `actual` >> asm_rewrite_tac[] >>
 fs[abi_encoder_registered_effect_def, frag_ids_def] >>
 rpt strip_tac >>
 `st.cs_next_id <= st'.cs_next_id` by
   (drule abi_decoder_to_buf_code >> simp[abi_decode_source_opcode_def, abi_decoder_code_def]) >>
 metis_tac[LESS_EQ_TRANS, NOT_LESS_EQUAL]
QED

Theorem ctor_checked_arg_emit_shape:
 emit_op opc ops st = (src,middle) ==>
 cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
 middle.cs_current_bb = st.cs_current_bb /\
 middle.cs_next_id = st.cs_next_id + 1 /\
 middle.cs_next_var = st.cs_next_var + 1
Proof
 strip_tac >>
 `isPREFIX st.cs_current_insts middle.cs_current_insts` by
   metis_tac[emit_op_prefix] >>
 gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
     fresh_var_def, fresh_id_def, comp_return_def, emit_def] >>
 irule cs_extends_same_block >> simp[]
QED

Theorem ctor_checked_arg_sequence_reach:
 inst_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
 middle.cs_current_bb = st.cs_current_bb /\
 EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
            i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
   (emitted_insts st middle) /\
 run_inst_seq_mem_ok (emitted_insts st middle) initial /\
 run_inst_seq (emitted_insts st middle) initial = OK raw /\
 raw.vs_allocas = initial.vs_allocas /\ raw.vs_current_bb = initial.vs_current_bb /\
 alloca_history func initial /\
 fn_has_code st middle func /\ ~initial.vs_halted /\
 initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 abi_decode_sim ctx func initial (raw with vs_inst_idx := LENGTH middle.cs_current_insts) /\
 gas_path_mem ctx func initial 0 (OK (raw with vs_inst_idx := LENGTH middle.cs_current_insts)) /\
 raw.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func (raw with vs_inst_idx := LENGTH middle.cs_current_insts)
Proof
 strip_tac >>
 drule_all ctor_checked_emitted_endpoint >>
 disch_then (qspec_then `ctx` strip_assume_tac) >>
 asm_rewrite_tac[] >>
 `frag_exec ctx st middle (\s. s = initial)
   (\t. t = raw with vs_inst_idx := LENGTH middle.cs_current_insts) (K F)` by
   (irule frag_exec_run_inst_seq >>
    fs[inst_extends_def, EVERY_CONJ] >> rpt strip_tac >> simp[] >>
    qexists `raw` >> simp[]) >>
 drule abi_decode_sim_from_fragment >>
 disch_then drule >> simp[]
QED

Theorem ctor_checked_arg_add_mem_ok:
 emit_op ADD [lhs;rhs] st = (out,middle) ==>
 run_inst_seq_mem_ok (emitted_insts st middle) initial
Proof
 strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
 irule ctor_arithmetic_tail_mem_ok >> simp[mk_inst_def]
QED

Theorem ctor_checked_arg_add_reach:
 emit_op ADD [lhs;rhs] st = (out,middle) /\
 eval_operand lhs initial = SOME a /\ eval_operand rhs initial = SOME b /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 alloca_history func initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared.
 eval_operand out prepared = SOME (a+b) /\ fresh_vars_wrt middle prepared /\
 (!op. abi_decoder_operand_live st.cs_next_var op ==>
   eval_operand op prepared = eval_operand op initial) /\
 prepared = (update_var (STRING #"%" (toString st.cs_next_var)) (a+b) initial
   with vs_inst_idx := LENGTH middle.cs_current_insts) /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 abi_decode_sim ctx func initial prepared /\
 gas_path_mem ctx func initial 0 (OK prepared) /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared
Proof
 strip_tac >> drule ctor_checked_arg_emit_shape >> strip_tac >>
 `fresh_vars_wrt middle initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 drule abi_decoder_binary_reentry >> simp_tac bool_ss [] >>
 disch_then drule >> disch_then drule >>
 disch_then (qspec_then `middle` mp_tac) >> simp[] >> strip_tac >>
 `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
    (emitted_insts st middle)` by
   (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
 `run_inst_seq_mem_ok (emitted_insts st middle) initial` by
   (irule ctor_checked_arg_add_mem_ok >> goal_assum (drule_at Any)) >>
 qmatch_asmsub_abbrev_tac `run_inst_seq _ initial = OK raw` >>
 `raw.vs_allocas = initial.vs_allocas /\ raw.vs_current_bb = initial.vs_current_bb` by
   simp[Abbr `raw`, update_var_def] >>
 drule_all ctor_checked_arg_sequence_reach >>
 disch_then (qspec_then `ctx` assume_tac) >>
 gvs[Abbr `raw`, eval_op_inst_idx, fresh_vars_wrt_def, update_var_def] >>
 asm_rewrite_tac[]
QED

Theorem ctor_checked_arg_read_mem_ok:
 emit_op DLOAD [src] st = (out,middle) /\
 eval_operand src initial = SOME (n2w p) /\ p < dimword (:256) /\
 p + 32 <= LENGTH initial.vs_data_section ==>
 run_inst_seq_mem_ok (emitted_insts st middle) initial
Proof
 strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
 simp[run_inst_seq_mem_ok_last, mk_inst_def, inst_dload_in_section_def,
      w2n_n2w] >>
 irule below_frontier_no_ranges >> simp[]
QED

Theorem ctor_checked_arg_read_reach:
 emit_op DLOAD [src] st = (out,middle) /\
 eval_operand src initial = SOME (n2w p) /\ p < dimword (:256) /\
 p + 32 <= LENGTH initial.vs_data_section /\
 fresh_vars_wrt st initial /\ fn_has_code st middle func /\
 alloca_history func initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?prepared.
 eval_operand out prepared = SOME (abi_decode_load DLOAD (n2w p : bytes32) initial) /\
 fresh_vars_wrt middle prepared /\
 (!op. abi_decoder_operand_live st.cs_next_var op ==>
   eval_operand op prepared = eval_operand op initial) /\
 prepared = (update_var (STRING #"%" (toString st.cs_next_var))
   (abi_decode_load DLOAD (n2w p : bytes32) initial) initial
   with vs_inst_idx := LENGTH middle.cs_current_insts) /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 abi_decode_sim ctx func initial prepared /\
 gas_path_mem ctx func initial 0 (OK prepared) /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared
Proof
 strip_tac >> drule ctor_checked_arg_emit_shape >> strip_tac >>
 `fresh_vars_wrt middle initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 drule abi_decoder_read_reentry >> simp_tac bool_ss [abi_decode_source_opcode_def] >>
 disch_then drule >>
 disch_then (qspec_then `middle` mp_tac) >> simp[] >> strip_tac >>
 `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
    (emitted_insts st middle)` by
   (drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]) >>
 `run_inst_seq_mem_ok (emitted_insts st middle) initial` by
   (drule_all ctor_checked_arg_read_mem_ok >> simp[]) >>
 qmatch_asmsub_abbrev_tac `run_inst_seq _ initial = OK raw` >>
 `raw.vs_allocas = initial.vs_allocas /\ raw.vs_current_bb = initial.vs_current_bb` by
   simp[Abbr `raw`, update_var_def] >>
 drule_all ctor_checked_arg_sequence_reach >>
 disch_then (qspec_then `ctx` assume_tac) >>
 gvs[Abbr `raw`, eval_op_inst_idx, fresh_vars_wrt_def, update_var_def] >>
 asm_rewrite_tac[]
QED

Theorem ctor_checked_arg_dynamic_head_section:
 i < LENGTH atys /\ LENGTH avs = LENGTH atys /\ has_types atys avs /\
 is_dynamic (EL i atys) /\
 LENGTH (enc (Tuple atys) (ListV avs)) <= LENGTH initial.vs_data_section /\
 LENGTH (enc (Tuple atys) (ListV avs)) < dimword (:256) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) ==>
 off + 32 <= LENGTH initial.vs_data_section /\ off < dimword (:256)
Proof
 strip_tac >>
 `TAKE i atys ++ EL i atys::DROP (SUC i) atys = atys` by
   (mp_tac (Q.ISPEC `atys:abi_type list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
    asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
 `TAKE i avs ++ EL i avs::DROP (SUC i) avs = avs` by
   (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `i:num` TAKE_DROP_SUC)) >>
    asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
 mp_tac (Q.INST [`pre` |-> `TAKE i atys`, `ty` |-> `EL i atys`,
   `post` |-> `DROP (SUC i) atys`, `pvs` |-> `TAKE i avs`,
   `v` |-> `EL i avs`, `rest` |-> `DROP (SUC i) avs`]
   abi_tuple_child_offset_ranges) >>
 simp[abi_member_head_size_def, Excl "enc_def"] >> strip_tac >> decide_tac
QED

Theorem ctor_checked_scratch_extend[local]:
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

Theorem ctor_checked_setup_effect_transport[local]:
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
 irule ctor_checked_scratch_extend >>
 qexistsl [`frag_ids middle st'`, `outs`, `initial`] >> simp[] >>
 rpt strip_tac >> fs[frag_ids_def] >> metis_tac[]
QED

Theorem ctor_checked_arg_setup_decode_actual:
 !pvar sb st src middle ce ty data_size st' env tv av v initial prepared d func ctx site.
 cs_extends st middle /\ middle.cs_blocks = st.cs_blocks /\
 st.cs_next_id <= middle.cs_next_id /\ st.cs_next_var <= middle.cs_next_var /\
 abi_decode_sim ctx func initial prepared /\
 gas_path_mem ctx func initial 0 (OK prepared) /\
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared /\
 eval_operand src prepared = SOME (n2w sb) /\
 abi_decoder_operand_live middle.cs_next_var src /\
 fresh_vars_wrt middle prepared /\ alloca_inv prepared /\
 alloca_frontier_inv ctx func site prepared /\
 prepared.vs_allocas = initial.vs_allocas /\
 prepared.vs_alloca_next = initial.vs_alloca_next /\
 prepared.vs_data_section = initial.vs_data_section /\
 prepared.vs_call_ctx = initial.vs_call_ctx /\ prepared.vs_labels = initial.vs_labels /\
 abi_encoder_registered_effect {} [] initial prepared /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x prepared = SOME w) /\
 ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
 prepared.vs_inst_idx = LENGTH middle.cs_current_insts /\
 compile_abi_decode_to_buf (Var pvar) src DLOAD (Lit (n2w data_size))
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
 unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) ==>
 ?actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
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
 qpat_x_assum `st.cs_blocks = middle.cs_blocks` kall_tac >>
 `!aid. middle.cs_next_id <= aid ==> FLOOKUP prepared.vs_allocas aid = NONE` by
   (asm_rewrite_tac[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 qpat_assum `eval_operand src prepared = _` assume_tac >>
 drule ctor_checked_arg_decoder_actual >>
 disch_then (drule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
 disch_then (drule_at (Pat `eval_operand src prepared = _`)) >>
 disch_then (qspecl_then [`ctx`, `func`, `site`, `d`] mp_tac) >>
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
 drule_all ctor_checked_setup_effect_transport >> strip_tac >>
 `initial.vs_alloca_next <= actual.vs_alloca_next` by metis_tac[] >>
 `abi_decode_sim ctx func initial actual` by
   (irule abi_decode_sim_trans >> qexists `prepared` >> asm_rewrite_tac[]) >>
 `gas_path_mem ctx func initial 0 (OK actual)` by
   metis_tac[ctor_checked_path_append, ADD_0] >>
 qexists `actual` >> asm_rewrite_tac[] >>
 rpt gen_tac >> strip_tac >>
 `not_fresh_at middle x` by
   (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
 metis_tac[]
QED

Theorem ctor_checked_arg_register_observations:
 (alloca_inv (update_var x w s) <=> alloca_inv s) /\
 (alloca_inv (s with vs_inst_idx := ix) <=> alloca_inv s) /\
 (abi_encoder_registered_effect ids outs (update_var x w s) t <=>
   abi_encoder_registered_effect ids outs s t) /\
 (abi_encoder_registered_effect ids outs (s with vs_inst_idx := ix) t <=>
   abi_encoder_registered_effect ids outs s t)
Proof
 simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      abi_encoder_registered_effect_def, update_var_def]
QED

Theorem ctor_checked_arg_add_decode_actual:
 !ptr sb st src middle ce ty data_size st' env tv av v initial d func ctx site.
 emit_op ADD [Lit 0w; Lit (n2w sb)] st = (src,middle) /\
 compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
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
 qpat_x_assum `st.cs_current_bb = middle.cs_current_bb` kall_tac >>
 irule ctor_checked_arg_setup_decode_actual >> asm_simp_tac bool_ss [] >>
 goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `abi_decode_sim _ _ _ _`)) >>
 asm_rewrite_tac[] >>
 simp[Abbr `prepared`, ctor_checked_arg_register_observations,
      alloca_frontier_inv_def, abi_encoder_registered_effect_def, update_var_def] >>
 qexistsl [`av`, `env`, `sb`] >> simp[] >>
 Cases_on `data_size = 0` >> fs[]
QED

Theorem ctor_checked_arg_dynamic_setup:
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
 prepared.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func prepared
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

Theorem ctor_checked_arg_dynamic_decode_actual:
 !pvar sb off st head m1 rel m2 src middle ce ty data_size st' env tv av v initial d func ctx site.
 emit_op ADD [Lit 0w; Lit (n2w off)] st = (head,m1) /\
 emit_op DLOAD [head] m1 = (rel,m2) /\
 emit_op ADD [Lit 0w; rel] m2 = (src,middle) /\
 off < dimword (:256) /\ off + 32 <= LENGTH initial.vs_data_section /\
 abi_decode_load DLOAD (n2w off : bytes32) initial = n2w sb /\
 compile_abi_decode_to_buf (Var pvar) src DLOAD (Lit (n2w data_size))
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
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
 drule_all ctor_checked_arg_dynamic_setup >>
 disch_then (qspecl_then [`site`, `ctx`]
   (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS))) >>
 `abi_decoder_operand_live middle.cs_next_var src` by
   (irule abi_decoder_operand_live_fresh >> goal_assum (drule_at Any) >>
    goal_assum (drule_at Any)) >>
 irule ctor_checked_arg_setup_decode_actual >> asm_simp_tac bool_ss [] >>
 goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `abi_decode_sim _ _ initial prepared`)) >>
 asm_rewrite_tac[] >>
 qexistsl [`av`, `env`, `sb`] >> simp[]
QED

Theorem ctor_checked_arg_static_code[local]:
 !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var (ptr:string)) (type_memory_bytes ce ty)) /\
 ~is_abi_dynamic ce.ce_struct_fields ty ==>
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
     DLOAD (Lit (n2w data_size)) 0 =
 do src <- emit_op ADD [Lit 0w; Lit (n2w off)];
    compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
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
          var_location_decode_operand_def, compile_abi_decode_to_buf_def,
          compile_abi_decode_static_def, FUN_EQ_THM,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
     pairarg_tac >> simp[] >> pairarg_tac >> simp[]) >>
 simp[build_positional_arg_def, compile_decode_args_def,
      var_location_decode_operand_def, FUN_EQ_THM,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
 rpt gen_tac >> pairarg_tac >> simp[] >> pairarg_tac >> simp[]
QED

Theorem ctor_checked_arg_dynamic_code[local]:
 !ptr. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) (type_memory_bytes ce ty)) /\
 ~is_word_type ty /\ is_abi_dynamic ce.ce_struct_fields ty ==>
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
     DLOAD (Lit (n2w data_size)) 0 =
 do static_src <- emit_op ADD [Lit 0w; Lit (n2w off)];
    offset_val <- emit_op DLOAD [static_src];
    src <- emit_op ADD [Lit 0w; offset_val];
    compile_abi_decode_to_buf (Var ptr) src DLOAD (Lit (n2w data_size))
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

Theorem ctor_checked_decode_constructor_arg:
 !ce env fargs avs atys encoded i name ty tv v off data_size
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
 rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
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
        drule_all ctor_checked_selected_type >> simp[]) >>
     `off + 32 <= LENGTH initial.vs_data_section /\ off < dimword (:256)` by
       (drule_all ctor_checked_selected_type >> strip_tac >>
        irule ctor_checked_arg_dynamic_head_section >>
        qexistsl [`atys`, `avs`, `i`] >> gvs[Excl "enc_def"]) >>
     drule_all ctor_checked_arg_dynamic_code >> strip_tac >>
     qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
     pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
     pairarg_tac >> asm_simp_tac (srw_ss()) [] >>
     pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
     irule ctor_checked_arg_dynamic_decode_actual >> asm_rewrite_tac[] >>
     goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD [Lit 0w; _] _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op DLOAD _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_op ADD _ _ = _`)) >>
     asm_rewrite_tac[] >> qexistsl [`EL i avs`, `env`, `abi_tuple_child_offset atys avs i`] >>
     gvs[Excl "enc_def"]) >>
 drule_all ctor_checked_arg_static_code >> strip_tac >>
 qpat_x_assum `compile_decode_args _ _ _ _ _ _ _ = _` mp_tac >>
 asm_rewrite_tac[] >> simp_tac (srw_ss()) [comp_bind_def, LET_THM] >>
 pairarg_tac >> asm_simp_tac (srw_ss()) [] >> strip_tac >>
 irule ctor_checked_arg_add_decode_actual >> asm_rewrite_tac[] >>
 goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
 goal_assum (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
 asm_rewrite_tac[] >> qexistsl [`EL i avs`, `env`] >> gvs[Excl "enc_def"]
QED

Theorem ctor_checked_alloc_buffer_edge:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ fn_inst_ids_distinct func /\
 FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
 alloca_history func initial /\ alloca_inv initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts /\
 raw = update_var (STRING #"%" (toString st.cs_next_var))
   (n2w initial.vs_alloca_next)
   (initial with <| vs_allocas := initial.vs_allocas |+
     (st.cs_next_id,(initial.vs_alloca_next,n));
     vs_alloca_next := initial.vs_alloca_next+n |>) ==>
 gas_path_mem ctx func initial 0 (OK (raw with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
 raw.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func (raw with vs_inst_idx := LENGTH sa.cs_current_insts)
Proof
 strip_tac >>
 `emit_op ALLOCA [Lit (n2w n)] st = (buf.buf_operand,sa)` by
   (gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
    pairarg_tac >> gvs[]) >>
 drule ctor_checked_arg_emit_shape >> strip_tac >>
 `sa.cs_current_insts = st.cs_current_insts ++
   [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
     [STRING #"%" (toString st.cs_next_var)]]` by
   gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >>
 `?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb initial.vs_inst_idx = SOME
      (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString st.cs_next_var)])` by
   (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
    simp[get_instruction_def, EL_APPEND_EQN]) >>
 `step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
   [STRING #"%" (toString st.cs_next_var)]) initial = OK raw` by
   simp[step_inst_base_def, mk_inst_def, eval_operand_def, exec_alloca_def, w2n_n2w] >>
 ` (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
     [STRING #"%" (toString st.cs_next_var)]).inst_opcode = ALLOCA` by simp[mk_inst_def] >>
 drule_all ctor_checked_alloca_path >>
 disch_then (qspec_then `ctx` mp_tac) >>
 simp[mk_inst_def] >> gvs[update_var_def, ADD1]
QED

Theorem ctor_checked_alloc_buffer_run:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ alloca_inv initial /\
 alloca_frontier_inv ctx func site initial /\ fn_inst_ids_distinct func /\
 unit_alloca_budget ctx < dimword (:256) /\
 FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ alloca_history func initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?a. a = (update_var (STRING #"%" (toString st.cs_next_var))
     (n2w initial.vs_alloca_next)
     (initial with <| vs_allocas := initial.vs_allocas |+
       (st.cs_next_id,(initial.vs_alloca_next,n));
       vs_alloca_next := initial.vs_alloca_next+n |>))
     with vs_inst_idx := LENGTH sa.cs_current_insts /\
   alloca_inv a /\ alloca_frontier_inv ctx func site a /\
   initial.vs_alloca_next+n < dimword (:256) /\
   ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
   abi_decode_sim ctx func initial a /\
   gas_path_mem ctx func initial 0 (OK a) /\
   a.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func a
Proof
 strip_tac >> drule_all ctor_alloc_buffer_run >> strip_tac >>
 qexists `a` >> asm_rewrite_tac[] >>
 qmatch_goalsub_abbrev_tac `OK (raw with vs_inst_idx := _)` >>
 `raw = update_var (STRING #"%" (toString st.cs_next_var))
   (n2w initial.vs_alloca_next)
   (initial with <| vs_allocas := initial.vs_allocas |+
     (st.cs_next_id,(initial.vs_alloca_next,n));
     vs_alloca_next := initial.vs_alloca_next+n |>)` by simp[Abbr `raw`] >>
 drule_all ctor_checked_alloc_buffer_edge >>
 disch_then (qspec_then `ctx` mp_tac) >> simp_tac (srw_ss()) []
QED

Theorem ctor_checked_alloc_buffer_actual:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ local_ptrs_rel func ce scopes initial /\
 fresh_vars_wrt st initial /\ alloca_inv initial /\ alloca_history func initial /\
 alloca_frontier_inv ctx func site initial /\ fn_inst_ids_distinct func /\
 unit_alloca_budget ctx < dimword (:256) /\
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
   alloca_inv a /\ alloca_frontier_inv ctx func site a /\
   fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
   (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
   (!name b sz. local_region ce scopes a name b sz ==>
     loweringStateRelDefs$regions_disjoint initial.vs_alloca_next n b sz) /\
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
   a.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func a
Proof
 strip_tac >>
 `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >>
 drule_all ctor_checked_alloc_buffer_run >> strip_tac >>
 `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
 `not_scope_ptr ce scopes (STRING #"%" (toString st.cs_next_var))` by
   (irule local_ptrs_rel_fresh_not_scope_ptr >>
    qexistsl [`func`, `initial`, `st`] >> simp[GREATER_EQ]) >>
 `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) =
    OK (a with vs_inst_idx := initial.vs_inst_idx)` by
   gvs[exec_alloca_def, mk_inst_def, update_var_def, w2n_n2w,
       venom_state_component_equality] >>
 drule local_ptrs_rel_exec_alloca_fresh >> simp[mk_inst_def, IgnAsm `a = _`] >>
 disch_then (qspecl_then [`func`, `ce`, `scopes`] mp_tac) >>
 simp[local_ptrs_rel_inst_idx, IgnAsm `a = _`] >> strip_tac >>
 `w = n2w initial.vs_alloca_next` by metis_tac[n2w_w2n] >>
 drule compile_alloc_buffer_parts >> strip_tac >>
 qexists `a` >>
 asm_rewrite_tac[] >>
 simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
 conj_tac
 >- (simp[local_backed_def] >> disj1_tac >>
     qexists `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]` >>
     drule_all entry_alloc_buffer_inst >> gvs[mk_inst_def]) >>
 conj_tac
 >- (fs[fresh_vars_wrt_def, update_var_def, GREATER_EQ] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 conj_tac
 >- (rpt strip_tac >>
     qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     fs[local_region_def, lookup_var_def, update_var_def] >> metis_tac[]) >>
 conj_tac
 >- (rpt strip_tac >> IF_CASES_TAC >> gvs[lookup_var_def]) >>
 simp[abi_encoder_registered_effect_def, frag_ids_def, GSPECIFICATION,
      update_var_def, FLOOKUP_UPDATE] >>
 rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem ctor_checked_register_one_actual:
 !ce env fargs avs atys encoded i name ty entry off data_size old
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce' [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all ctor_checked_alloc_buffer_actual >>
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
 drule_all ctor_checked_decode_constructor_arg >>
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

Resume ctor_checked_register_one_actual[finish]:
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

Resume ctor_checked_register_one_actual[locals]:
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

Resume ctor_checked_register_one_actual[effect]:
 irule ctor_registered_alloc_decode_effect >>
 qexistsl [`a`, `st.cs_next_id`, `frag_ids st sa`, `initial.vs_alloca_next`,
   `frag_ids sa st'`, `type_memory_bytes ce' ty`] >>
 asm_rewrite_tac[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Resume ctor_checked_register_one_actual[registers]:
 rpt strip_tac >>
 `not_fresh_at sa x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 metis_tac[]
QED

Finalise ctor_checked_register_one_actual

Theorem ctor_checked_register_suffix_actual:
 !rest ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial.
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
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
 qpat_x_assum `!ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial. _`
   (mk_asm "suffix_ih") >>
 qpat_x_assum `EVERY (\a. ?off. _) (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 qpat_x_assum `EVERY _ (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 `FLOOKUP (ce0 with ce_vars := vars).ce_vars h0 =
    SOME (MemLoc off (type_memory_bytes (ce0 with ce_vars := vars) h1))` by simp[] >>
 suspend "phases"
QED

Resume ctor_checked_register_suffix_actual[phases]:
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
 drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) ctor_checked_register_one_actual >>
 disch_then (drule_at (Pat `EL _ _ = _`)) >>
 disch_then (drule_at (Pat `_ = enc _ _`)) >>
 disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
 disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
 disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
 disch_then (qspecl_then [`env`, `off`] mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `middle` (map_every assume_tac o CONJUNCTS)) >>
 suspend "recurse"
QED

Resume ctor_checked_register_suffix_actual[recurse]:
 `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env h1` by
   (irule ctor_checked_selected_type >> goal_assum (drule_at Any) >> simp[]) >>
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
 disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
 disch_then (qspec_then `env` mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 asm_x "suffix_ih" kall_tac >> suspend "finish"
QED

Resume ctor_checked_register_suffix_actual[finish]:
 `gas_path_mem ctx func initial 0 (OK actual)` by
   metis_tac[ctor_checked_path_append, ADD_0] >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- suspend "suffix_effect" >>
 conj_tac >- suspend "suffix_registers" >>
 metis_tac[abi_decode_sim_trans]
QED

Resume ctor_checked_register_suffix_actual[suffix_effect]:
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

Resume ctor_checked_register_suffix_actual[suffix_registers]:
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

Finalise ctor_checked_register_suffix_actual

Theorem ctor_checked_register_args:
 !ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial.
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
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
 alloca_history func initial /\ unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
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
 actual.vs_gas_readings = initial.vs_gas_readings /\ alloca_history func actual
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 irule ctor_checked_register_suffix_actual >> asm_rewrite_tac[] >>
 qexistsl [`atys`, `avs`, `ce0`, `data_size`, `encoded`, `env`, `fargs`, `0`, `fargs`,
   `ce0.ce_vars`] >> simp[]
QED
