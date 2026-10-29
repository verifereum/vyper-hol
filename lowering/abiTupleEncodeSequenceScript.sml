(* Execute every actual tuple slot, preserving complete nonword sources for
   later slots and complete child input already written by earlier slots. *)
Theory abiTupleEncodeSequence
Ancestors
  abiTupleEncodeCode abiTupleEncodeSlot abiTupleEncodeResult abiTupleEncodeInput
  abiTupleEncodeMemory abiTupleProps abiDecoderReentry abiDecoderContract
  abiDecoderFrameCompose compileEnv exprLowering emitHelperProps exprLoweringProps
  venomState venomExecSemantics words list arithmetic

Theorem abi_tuple_encode_tail_inputs:
  abi_tuple_encode_result sf ce [(op,ty)] [at] [av] st middle limit_st d s t /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  st.cs_next_var <= middle.cs_next_var /\ lo <= d /\ d+type_memory_bytes ce ty <= hi ==>
  abi_tuple_encode_inputs sf ce xs ats avs middle.cs_next_var lo hi t
Proof
  strip_tac >> qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [abi_tuple_encode_result_def, abi_tuple_bytes_def]) >>
  `lo <= hi` by decide_tac >>
  `abi_decode_frame lo (hi-lo) s t` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `type_memory_bytes ce ty`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  drule_all abi_tuple_encode_inputs_transport >> simp[]
QED

Theorem abi_tuple_encode_sequence:
  !xs ce buf off st final s baddr ats avs lo hi.
  compile_store_abi_tuple ce buf off xs st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ abi_decoder_operand_live st.cs_next_var buf /\
  lo <= baddr+off /\ baddr+off+abi_tuple_bytes ce xs <= hi /\ hi < dimword (:256) /\
  abi_tuple_encode_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_encode_result sf ce xs ats avs st final limit_st (baddr+off) s actual
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_encode_inputs_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[abi_tuple_encode_result_def, emitted_insts_def, run_inst_seq_def, inst_extends_refl,
        abi_tuple_encode_memory_def, abi_tuple_bytes_def, abi_decode_frame_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[abi_tuple_encode_inputs_def] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  rename1 `abi_tuple_encode_input sf ce h1 head_at head_av h0 st.cs_next_var lo hi s` >>
  rename1 `abi_tuple_encode_inputs sf ce xs tail_ats tail_avs st.cs_next_var lo hi s` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var /\
   baddr+off < dimword (:256) /\ lo <= hi /\ baddr+off+type_memory_bytes ce h1 <= hi /\
   lo <= baddr+(off+type_memory_bytes ce h1) /\
   baddr+(off+type_memory_bytes ce h1)+abi_tuple_bytes ce xs <= hi` by
    (fs[abi_tuple_bytes_def] >> decide_tac) >>
  drule_all abi_tuple_encode_result_slot >> strip_tac >>
  rename1 `abi_tuple_encode_result sf ce [(h0,h1)] [head_at] [head_av] st middle limit_st (baddr+off) s written` >>
  drule_all abi_tuple_encode_tail_inputs >> strip_tac >>
  qpat_assum `abi_tuple_encode_result _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_tuple_encode_result_def]) >>
  `eval_operand buf written = SOME (n2w baddr)` by (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live middle.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  qpat_x_assum `!ce buf off st final s baddr ats avs lo hi. _`
    (qspecl_then [`ce`, `buf`, `off+type_memory_bytes ce h1`, `middle`, `final`, `written`,
      `baddr`, `tail_ats`, `tail_avs`, `lo`, `hi`] (mp_tac o PURE_REWRITE_RULE [ADD_ASSOC])) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `abi_tuple_encode_result sf ce xs tail_ats tail_avs middle final limit_st _ written actual` >>
  qexists_tac `actual` >> RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  mp_tac (Q.INST [`op` |-> `h0`, `ty` |-> `h1`, `at` |-> `head_at`, `av` |-> `head_av`,
    `ats` |-> `tail_ats`, `avs` |-> `tail_avs`, `d` |-> `baddr+off`,
    `t` |-> `written:venom_state`, `u` |-> `actual:venom_state`]
    (Q.ISPEC `h0:operand` (Q.GEN `op` abi_tuple_encode_result_cons))) >>
  asm_simp_tac bool_ss [ADD_ASSOC]
QED
