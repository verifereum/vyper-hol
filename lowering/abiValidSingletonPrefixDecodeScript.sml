(* Execute a dynamic singleton at its actual input offset, then decode the
   child's canonical prefix with the established recursive decoder. *)
Theory abiValidSingletonPrefixDecode
Ancestors
  abiValidSingletonPrefixEntry abiValidSingletonPrefixInput abiValidSingletonCode
  abiDecoderCoherentCorrect abiDecoderArrayBody abiDecoderCoherence abiDecoderDynamic
  abiDecoderValidRecursive abiDecoderValidContract abiDecoderValidWrapping
  valueEncodingProps vyperTyping abiBoundaryChecks
  abiDecoderEffect abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiDecoderAllocation abiDecoderDynamicLoopSetup abiDecoderLoop
  abiEncoder fragExec compileEnv valueEncoding vyperABI contractABI
  venomState venomExecSemantics words list pair arithmetic

Theorem abi_valid_singleton_prefix_decode_offset:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex T [(type_to_abi_dec_info sf ce ty,32,type_memory_bytes ce ty)])
    start = ((),end_st) /\ fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v start src dst opc hi sb d b cap initial /\
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc /\ abi_decoder_coherent ce env sf ty tv /\
   is_dynamic (vyper_to_abi_type env ty)` by
    fs[abi_valid_singleton_prefix_pre_def, abi_decoder_ranges_def,
       Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  `abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    (drule abi_decoder_coherent_dynamic >> asm_simp_tac bool_ss []) >>
  drule_all abi_valid_dynamic_singleton_trace >> strip_tac >>
  drule_all abi_valid_singleton_child_code >> strip_tac >>
  Cases_on `ops` >> RULE_ASSUM_TAC (SIMP_RULE bool_ss [FST, SND]) >>
  rename1 `abi_decode_singleton_setup dst src opc hi start = ((childsrc,childdst),middle)` >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_valid_singleton_prefix_entry >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  SUBGOAL_THEN ``middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0`` assume_tac
  >- asm_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`start` |-> `middle`, `end_st` |-> `end_st`,
    `initial` |-> `prepared:venom_state`, `dst` |-> `childdst`, `src` |-> `childsrc`,
    `sb` |-> `sb + abi_head_word bs`] abi_decoder_decode) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v d actual.vs_memory` >>
  `abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual` by
    (mp_tac (Q.INST [`lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
      `next` |-> `start.cs_next_var`, `child_lo` |-> `middle.cs_next_id`,
      `child_next` |-> `middle.cs_next_var`, `s` |-> `initial:venom_state`,
      `prepared` |-> `prepared:venom_state`, `t` |-> `actual:venom_state`,
      `d` |-> `d:num`, `sz` |-> `type_memory_bytes ce ty`] abi_decoder_address_then_effect) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

Theorem abi_valid_singleton_parent_pre:
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v st src dst opc hi sb d b cap initial ==>
  abi_decoder_valid_pre ce env sf (TupleT [ty]) (TupleTV [tv]) bs
    (ArrayV (TupleV [v])) st src dst opc hi sb d b cap initial
Proof
  simp_tac bool_ss [abi_valid_singleton_prefix_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf (TupleT [ty]) (TupleTV [tv])` by
    (drule abi_decoder_coherent_singleton >> simp[]) >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  `1 < dimword (:256)` by simp[dimword_def] >>
  `abi_decoder_metadata ce env (TupleT [ty]) (TupleTV [tv])
    (type_to_abi_dec_info ce.ce_struct_fields ce (TupleT [ty]))
    (dec (vyper_to_abi_type env (TupleT [ty])) bs) (ArrayV (TupleV [v]))` by
    (irule abi_decoder_coherent_root_metadata >>
     asm_simp_tac (srw_ss()) [LET_THM, vyper_to_abi_type_def, value_has_type_def,
       has_type_def, valid_length_def, abi_to_vyper_def] >>
     qexists_tac `sf` >> asm_simp_tac bool_ss []) >>
  asm_simp_tac (srw_ss()) [abi_decoder_valid_pre_def, vyper_to_abi_type_def,
    type_memory_bytes_def, is_dynamic_def]
QED

Theorem abi_valid_singleton_prefix_decode:
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex T [(type_to_abi_dec_info sf ce ty,32,type_memory_bytes ce ty)])
    start = ((),end_st) /\ fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_valid_singleton_prefix_pre ce env sf ty tv bs av v start src dst opc hi sb d b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. val_in_memory tv v d actual.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv /\ is_dynamic (vyper_to_abi_type env ty)` by
    fs[abi_valid_singleton_prefix_pre_def, Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_decoder_singleton_info >> disch_then assume_tac >>
  drule abi_valid_singleton_parent_pre >> disch_then assume_tac >>
  mp_tac (Q.INST [`ty` |-> `TupleT [ty]`, `tv` |-> `TupleTV [tv]`,
    `v` |-> `ArrayV (TupleV [v])`] abi_decoder_valid_decode) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists_tac `actual` >>
  fs[singleton_tuple_memory_sizes, val_in_memory_singleton_tuple]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_SINGLETON_PREFIX_DECODE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid singleton prefix decoding not kernel closed: " ^ n)
  end) (DB.thms "abiValidSingletonPrefixDecode");
