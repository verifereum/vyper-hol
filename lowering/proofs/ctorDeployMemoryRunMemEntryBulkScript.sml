Theory ctorDeployMemoryRunMemEntryBulk
Ancestors
 ctorDeployMemoryRunMemEntryArraySteps ctorDeployMemoryRunMemEntryBytes
 ctorDeployMemoryRunMemEntryWord
 abiDecoderBulk abiDecoderBulkExecute abiDecoderBulkReentry ctorAbiActualBulk
 abiDecoderReentry ctorDeployMemoryRunMemEntryReentry
 fragGasSeqMem fragGasPathMem allocaHistory fragExec instIdxIndep
 ctorAbiActualWorld abiEncoderRegisteredEffect
 abiDecoderComposition abiDecoderContract abiDecoderCopy abiDecoderGuards
 abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderArrayHeader
 abiDecoderReservation abiDecoderArrayLoopInit abiDecoderDynarrayPrefix
 abiStaticLayoutProps abiStaticAggregateProps abiStaticDynarrayLayout
 abiDecoderTypedContract abiDecoderContract abiEncoder valueEncoding vyperABI byte
 emitHelperProps emitHelper exprLoweringProps compileEnv venomInst venomExecSemantics
 instMemFrontier memSafeRun fragExecMem venomState words list rich_list arithmetic

Theorem ctor_bulk_copy_mem_ok:
 !dst src size st st' s sb d k.
 emit_void DLOADBYTES [dst;src;size] st = ((),st') /\
 eval_operand src s = SOME (n2w sb) /\
 eval_operand dst s = SOME (n2w d) /\
 eval_operand size s = SOME (n2w k) /\
 sb < dimword (:256) /\ d < dimword (:256) /\ k < dimword (:256) /\
 sb+k <= LENGTH s.vs_data_section /\ d+k <= s.vs_alloca_next ==>
 run_inst_seq_mem_ok (emitted_insts st st') s
Proof
 rpt strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
 simp[run_inst_seq_mem_ok_last] >> conj_tac
 >- simp[below_frontier_DLOADBYTES, w2n_n2w] >>
 simp[inst_dload_in_section_def, mk_inst_def] >> rpt strip_tac >>
 gvs[w2n_n2w]
QED

Theorem ctor_bulk_arithmetic_emit:
 emit_op opc args st = (v,st') /\ (opc = ADD \/ opc = MUL) ==>
 run_inst_seq_mem_ok (emitted_insts st st') s /\
 (!t. run_inst_seq (emitted_insts st st') s = OK t ==>
      t.vs_alloca_next = s.vs_alloca_next)
Proof
 disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
 drule emitted_insts_emit_op >> strip_tac >> conj_tac
 >- (qpat_x_assum `opc = ADD \/ opc = MUL` strip_assume_tac >>
     simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
 rpt strip_tac >>
 `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode /\
               i.inst_opcode <> ALLOCA) (emitted_insts st st')` by
   (simp[mk_inst_def] >> gvs[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def]) >>
 drule_all ctorAbiActualWorldTheory.ctor_actual_sequence_no_alloca >> simp[]
QED

Theorem ctor_bulk_payload_mem_ok:
 abi_decode_bulk_payload dst src cnt mem_sz DLOAD (Lit 0w) st = ((),st') /\
 eval_operand src s = SOME (n2w sb) /\
 eval_operand dst s = SOME (n2w d) /\
 eval_operand cnt s = SOME (n2w n) /\
 sb+32 < dimword (:256) /\ d+32 < dimword (:256) /\
 n*mem_sz < dimword (:256) /\
 sb+32+n*mem_sz <= LENGTH s.vs_data_section /\
 d+32+n*mem_sz <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
 run_inst_seq_mem_ok (emitted_insts st st') s
Proof
 simp[abi_decode_bulk_payload_def, comp_bind_def,
      compile_abi_dec_addr_def, comp_return_def] >>
 pairarg_tac >> strip_tac >> gvs[] >>
 pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
 rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
 rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
 rename1 `emit_op ADD [dst; Lit 32w] c2 = (dst_data,c3)` >>
 `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by
   simp[eval_operand_def] >>
 drule_all abi_decode_mul_sequence >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
 gvs[word_mul_n2w] >>
 `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
 `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
 drule_all abi_decode_add_sequence >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
 `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
 `eval_operand (Lit 32w) s2 = SOME 32w` by simp[eval_operand_def] >>
 drule_all (Q.INST [`st` |-> `c2`, `s` |-> `s2`] abi_decode_add_sequence) >>
 strip_tac >>
 rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
 `run_inst_seq_mem_ok (emitted_insts st c1) s /\
  s1.vs_alloca_next = s.vs_alloca_next` by
   (qpat_assum `emit_op MUL _ st = _`
      (mp_then Any mp_tac ctor_bulk_arithmetic_emit) >> simp[] >>
    disch_then (qspec_then `s` mp_tac) >> simp[]) >>
 `run_inst_seq_mem_ok (emitted_insts c1 c2) s1 /\
  s2.vs_alloca_next = s1.vs_alloca_next` by
   (qpat_assum `emit_op ADD _ c1 = _`
      (mp_then Any mp_tac ctor_bulk_arithmetic_emit) >> simp[] >>
    disch_then (qspec_then `s1` mp_tac) >> simp[]) >>
 `run_inst_seq_mem_ok (emitted_insts c2 c3) s2 /\
  s3.vs_alloca_next = s2.vs_alloca_next` by
   (qpat_assum `emit_op ADD _ c2 = _`
      (mp_then Any mp_tac ctor_bulk_arithmetic_emit) >> simp[] >>
    disch_then (qspec_then `s2` mp_tac) >> simp[]) >>
 `eval_operand src_data s3 = SOME (n2w (sb+32)) /\
  eval_operand sz_op s3 = SOME (n2w (n*mem_sz))` by
   (simp[GSYM word_add_n2w] >> metis_tac[MULT_COMM]) >>
 `run_inst_seq_mem_ok (emitted_insts c3 st') s3` by
   (irule ctor_bulk_copy_mem_ok >>
    qexistsl [`d+32`, `dst_data`, `n*mem_sz`, `sb+32`, `sz_op`, `src_data`] >>
    gvs[abi_decode_copy_opcode_def, word_add_n2w] >> decide_tac) >>
 `inst_extends c3 st'` by (drule inst_extends_emit_void >> simp[]) >>
 `run_inst_seq_mem_ok (emitted_insts c2 st') s2` by
   (irule ctor_checked_emitted_mem_chain >> qexistsl [`c3`, `s3`] >> simp[]) >>
 `inst_extends c2 st'` by metis_tac[inst_extends_trans] >>
 `run_inst_seq_mem_ok (emitted_insts c1 st') s1` by
   (irule ctor_checked_emitted_mem_chain >> qexistsl [`c2`, `s2`] >> simp[]) >>
 irule ctor_checked_emitted_mem_chain >> qexistsl [`c1`, `s1`] >>
 simp[] >> metis_tac[inst_extends_trans]
QED

Theorem ctor_bulk_header_allocation_shape[local]:
 abi_decode_array_header dst src DLOAD st = (cnt,st') ==>
 EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
   (emitted_insts st st')
Proof
 simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
 simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
 simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem ctor_bulk_body_mem_ok:
 abi_decode_bulk_body dst src src DLOAD (Lit 0w) mem_sz st = ((),st') /\
 eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
 abi_decode_load DLOAD (n2w sb : bytes32) s = n2w n /\
 sb+32 < dimword (:256) /\ d+32 < dimword (:256) /\
 n*mem_sz < dimword (:256) /\ fresh_vars_wrt st s /\
 abi_decoder_operand_live st.cs_next_var dst /\
 sb+32+n*mem_sz <= LENGTH s.vs_data_section /\
 d+32+n*mem_sz <= s.vs_alloca_next ==>
 run_inst_seq_mem_ok (emitted_insts st st') s
Proof
 simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
 pairarg_tac >> strip_tac >> gvs[] >>
 rename1 `abi_decode_array_header dst src DLOAD st = (cnt,c1)` >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `d < dimword (:256) /\ sb < dimword (:256)` by decide_tac >>
 drule_all abi_decode_array_header_sequence >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
 `eval_operand src s1 = SOME (n2w sb) /\
  eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
 drule ctor_bulk_header_allocation_shape >> strip_tac >>
 `s1.vs_alloca_next = s.vs_alloca_next` by
   (drule_all abi_decode_sequence_allocation_frame >> simp[]) >>
 `s1.vs_data_section = s.vs_data_section` by gvs[abi_decode_frame_def] >>
 `run_inst_seq_mem_ok (emitted_insts st c1) s` by
   (irule ctor_checked_array_count_header_mem_ok >>
    qexistsl [`cnt`, `d`, `dst`, `sb`, `src`] >> simp[] >> decide_tac) >>
 `run_inst_seq_mem_ok (emitted_insts c1 st') s1` by
   (irule ctor_bulk_payload_mem_ok >> simp[] >>
    qexistsl [`cnt`, `d`, `dst`, `mem_sz`, `n`, `sb`, `src`] >> simp[]) >>
 drule abi_decode_bulk_payload_sequence >>
 disch_then (qspecl_then [`0`, `sb`, `s1`, `n`, `d`] mp_tac) >>
 (impl_tac >- simp[eval_operand_def]) >> strip_tac >>
 irule ctor_checked_emitted_mem_chain >> qexistsl [`c1`, `s1`] >> simp[]
QED

Theorem ctor_bulk_sequence_mem_ok:
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi
   (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
 ~dec_info_needs_clamp ei /\
 eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
 abi_decode_load DLOAD (n2w sb : bytes32) s = n2w n /\
 n <= maxn /\ maxn < dimword (:256) /\
 sb+32 < dimword (:256) /\ d+32 < dimword (:256) /\
 n*mem_sz < dimword (:256) /\
 (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    sb+32+n*abi_sz <= h /\ h < dimword (:256)) /\
 fresh_vars_wrt st s /\ abi_decoder_operand_live st.cs_next_var dst /\
 sb+32+n*mem_sz <= LENGTH s.vs_data_section /\
 d+32+n*mem_sz <= s.vs_alloca_next ==>
 run_inst_seq_mem_ok (emitted_insts st st') s
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
 asm_simp_tac bool_ss [abi_decode_bulk_phases, comp_ignore_bind_def,
                      comp_bind_def, LET_THM] >>
 pairarg_tac >> strip_tac >>
 qpat_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _`
   (strip_assume_tac o REWRITE_RULE [abi_decode_dynarray_position_prefix_zero_base_eq]) >>
 rename1 `abi_decode_dynarray_checked_prefix src DLOAD hi maxn abi_sz st = ((),c1)` >>
 qpat_x_assum `_ = ((),st')` mp_tac >>
 asm_rewrite_tac[] >> disch_tac >>
 drule_all abi_decode_dynarray_checked_prefix_sequence >> strip_tac >>
 rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
 `eval_operand src s1 = SOME (n2w sb) /\
  eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
 `abi_decode_load DLOAD (n2w sb : bytes32) s1 = n2w n` by
   gvs[abi_decode_load_def, abi_decode_source_def] >>
 `abi_decode_bulk_body dst src src DLOAD (Lit 0w) mem_sz c1 = ((),st')` by
   (qpat_x_assum `_ = ((),st')` mp_tac >>
    asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
 drule_all abi_decode_dynarray_checked_prefix_shape >> strip_tac >>
 `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st c1)` by (fs[EVERY_MEM] >> metis_tac[]) >>
 `s1.vs_alloca_next = s.vs_alloca_next` by
   (drule_all abi_decode_sequence_allocation_frame >> simp[]) >>
 `abi_decoder_operand_live c1.cs_next_var dst` by
   (irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
    qexists `st.cs_next_var` >> simp[]) >>
 `run_inst_seq_mem_ok (emitted_insts st c1) s` by
   (irule ctor_checked_array_prefix_mem_ok >>
    qexistsl [`abi_sz`, `hi`, `maxn`, `sb`, `src`] >> simp[] >> decide_tac) >>
 `run_inst_seq_mem_ok (emitted_insts c1 st') s1` by
   (irule ctor_bulk_body_mem_ok >> simp[] >>
    qexistsl [`d`, `dst`, `mem_sz`, `n`, `sb`, `src`] >> simp[]) >>
 mp_tac (Q.INST [`st` |-> `c1`, `s` |-> `s1`, `opc` |-> `DLOAD`,
   `base_op` |-> `Lit 0w`, `src_base` |-> `0`]
   abi_decode_bulk_body_sequence) >>
 (impl_tac >- simp[eval_operand_def]) >> strip_tac >>
 irule ctor_checked_emitted_mem_chain >> qexistsl [`c1`, `s1`] >> simp[]
QED

Theorem ctor_typed_bulk_mem_ok:
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi
   (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
 ~dec_info_needs_clamp ei /\
 abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
   (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
   (ListV avs) (ArrayV (DynArrayV vs)) st last src dst DLOAD (Lit 0w) hi 0 sb d b cap s /\
 abi_decoder_operand_live st.cs_next_var dst /\
 sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs))
   <= LENGTH s.vs_data_section /\
 d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= s.vs_alloca_next ==>
 run_inst_seq_mem_ok (emitted_insts st st') s
Proof
 strip_tac >> drule_all abi_decoder_bulk_pre_facts >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all static_same_canonical_layout >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule static_layout_compatible_properties >> strip_tac >>
 `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) =
   32 + LENGTH vs * type_memory_size tv` by
   simp[static_dynarray_encoding, LENGTH_word_to_bytes, Excl "enc_def"] >>
 `sb+32+LENGTH vs*mem_sz <= LENGTH s.vs_data_section /\
  d+32+LENGTH vs*mem_sz <= s.vs_alloca_next` by
   (gvs[vyper_to_abi_type_def, Excl "enc_def"] >> decide_tac) >>
 irule ctor_bulk_sequence_mem_ok >> simp[Excl "enc_def"] >>
 qexistsl [`abi_sz`, `d`, `dst`, `ei`, `hi`, `maxn`, `mem_sz`, `LENGTH vs`, `sb`, `src`] >>
 gnvs[Excl "enc_def"]
QED

Theorem ctor_bulk_reentry_mem_ok:
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi
   (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
 ~dec_info_needs_clamp ei /\
 abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
   (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
   (ListV avs) (ArrayV (DynArrayV vs)) st last src dst DLOAD (Lit 0w) hi 0 sb d b cap
   (abi_decoder_prune_vars st.cs_next_var initial) /\
 abi_decoder_operand_live st.cs_next_var dst /\
 sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs))
   <= LENGTH initial.vs_data_section /\
 d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next ==>
 run_inst_seq_mem_ok (emitted_insts st st') initial
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs))
     <= LENGTH (abi_decoder_prune_vars st.cs_next_var initial).vs_data_section /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <=
     (abi_decoder_prune_vars st.cs_next_var initial).vs_alloca_next` by
   gvs[abi_decoder_prune_vars_def, Excl "enc_def"] >>
 `run_inst_seq_mem_ok (emitted_insts st st')
   (abi_decoder_prune_vars st.cs_next_var initial)` by
   (drule_all ctor_typed_bulk_mem_ok >> simp[]) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all abi_decoder_typed_bulk_fields >> strip_tac >>
 irule ctor_reentry_sequence_mem >> conj_tac >- simp[] >>
 qexistsl [`initial.vs_vars`, `abi_decoder_prune_vars st.cs_next_var initial`, `t`] >>
 simp[abi_decoder_prune_extension]
QED

Theorem ctor_bulk_sequence_zero_path:
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecDynArray ei abi_sz mem_sz F maxn)
   st = ((),st') /\ ~dec_info_needs_clamp ei /\
 fn_has_code st st' func /\ ~s.vs_halted /\
 s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
 run_inst_seq_mem_ok (emitted_insts st st') s /\
 run_inst_seq (emitted_insts st st') s = OK t ==>
 gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
 t.vs_gas_readings = s.vs_gas_readings
Proof
 strip_tac >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
   (simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >> fs[EVERY_MEM] >>
    qpat_x_assum `!i. MEM i _ ==> abi_decoder_reentry_opcode _` drule >>
    simp[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def]) >>
 `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX st'.cs_current_insts bb.bb_instructions` by
   (gvs[fn_has_code_def] >> metis_tac[]) >>
 `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
         emitted_insts st st' = code` by
   (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
    simp[IS_PREFIX_APPEND] >> strip_tac >>
    simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
 `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
   (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
    simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
    rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
 `gas_path_mem ctx func s
    (LENGTH (FILTER (\i. i.inst_opcode = GAS) code))
    (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))` by
   (irule run_inst_seq_gas_path_mem >> gvs[] >> metis_tac[]) >>
 `gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH st'.cs_current_insts))` by gvs[] >>
 simp[] >> drule gas_path_mem_ok_suffix >> simp[]
QED

Theorem ctor_bulk_sequence_history:
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecDynArray ei abi_sz mem_sz F maxn)
   st = ((),st') /\ ~dec_info_needs_clamp ei /\
 fn_has_code st st' func /\ alloca_history func s /\
 s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
 t.vs_allocas = s.vs_allocas /\ t.vs_current_bb = s.vs_current_bb ==>
 alloca_history func (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
 strip_tac >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_shape >> strip_tac >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX st'.cs_current_insts bb.bb_instructions` by
   (gvs[fn_has_code_def] >> metis_tac[]) >>
 `?code. st'.cs_current_insts = st.cs_current_insts ++ code /\
         emitted_insts st st' = code` by
   (qpat_x_assum `isPREFIX st.cs_current_insts st'.cs_current_insts` mp_tac >>
    simp[IS_PREFIX_APPEND] >> strip_tac >>
    simp[emitted_insts_def, DROP_LENGTH_APPEND]) >>
 `isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions)` by
   (qpat_x_assum `isPREFIX st'.cs_current_insts _` mp_tac >>
    simp[IS_PREFIX_APPEND] >> strip_tac >> simp[IS_PREFIX_APPEND] >>
    rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> metis_tac[]) >>
 `EVERY (\i. i.inst_opcode <> ALLOCA) code` by
   (fs[EVERY_MEM] >> rpt strip_tac >> metis_tac[is_alloca_op_def]) >>
 `alloca_history func (t with vs_inst_idx := s.vs_inst_idx + LENGTH code)` by
   (irule ctor_sequence_history_advance >> qexistsl [`bb`, `code`, `s`] >> gvs[]) >>
 gvs[]
QED

Theorem ctor_checked_bulk_sequence:
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (DecDynArray ei abi_sz mem_sz F maxn)
   st = ((),st') /\ ~dec_info_needs_clamp ei /\
 abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
   (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
   (ListV avs) (ArrayV (DynArrayV vs)) st last src dst DLOAD (Lit 0w) hi 0 sb d b cap
   (abi_decoder_prune_vars st.cs_next_var initial) /\
 abi_decoder_operand_live st.cs_next_var dst /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs))
   <= LENGTH initial.vs_data_section /\
 d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= initial.vs_alloca_next /\
 fn_has_code st st' func /\ alloca_history func initial /\ ~initial.vs_halted /\
 initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. run_inst_seq (emitted_insts st st') initial = OK actual /\
   val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
   abi_decode_frame d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) initial actual /\
   fresh_vars_wrt limit_st actual /\
   (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
   actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
   abi_encoder_registered_effect {} [(d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))]
     initial actual /\
   actual.vs_current_bb = initial.vs_current_bb /\
   gas_path_mem ctx func initial 0
     (OK (actual with vs_inst_idx := LENGTH st'.cs_current_insts)) /\
   actual.vs_gas_readings = initial.vs_gas_readings /\
   alloca_history func (actual with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_bulk_reentry_sequence >> strip_tac >>
 drule_all ctor_bulk_reentry_mem_ok >> strip_tac >>
 drule_all ctor_bulk_sequence_zero_path >>
 disch_then (qspec_then `ctx` strip_assume_tac) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
 drule_all ctor_actual_sequence_world >> strip_tac >>
 drule_all ctor_actual_scratch_free_effect >>
 disch_then (qspecl_then [`site`, `{}`, `func`, `ctx`] strip_assume_tac) >>
 `actual.vs_current_bb = initial.vs_current_bb` by
   (drule_at (Pos hd)
      (Q.ISPEC `\s:venom_state. s.vs_current_bb` run_inst_seq_preserves_field) >>
    simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke]) >>
 drule_all ctor_bulk_sequence_history >> strip_tac >>
 qexists `actual` >> simp[]
QED
