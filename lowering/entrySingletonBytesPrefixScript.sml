(* Whole straight-line singleton setup and Bytes/String child execution. *)
Theory entrySingletonBytesPrefix
Ancestors
  entrySingletonValidInput entryWordPrefix abiValidSingletonReentry
  abiValidBytesReentry abiDecoderValidBytesInput abiDecoderBytesTyped
  abiValidSingletonSetup abiDecoderSingletonSetup abiDecoderGuards
  abiDecoderTypedCompose abiDecoderContract abiDecoderValidContract
  abiDecoderDynamicLoopSetup abiDecoderCoherence abiDecoderTypedContract
  entrySinkExtraction fragExec abiEncoderObserver instIdxIndep exprLoweringProps
  compileEnv valueEncoding vyperABI contractABI venomExecSemantics venomState
  emitHelperProps pair words list rich_list

Theorem decoder_valid_singleton_bytestring_local_prefix:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  abi_decode_singleton_setup dst src CALLDATALOAD (Lit 0w) st = ((childsrc,childdst),ready) /\
  compile_abi_decode_to_buf childdst childsrc CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) ready = ((),final) /\
  abi_valid_singleton_setup_pre st src dst CALLDATALOAD (Lit 0w) sb d (abi_head_word bs)
    (abi_decoder_prune_vars st.cs_next_var initial) /\
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  is_dynamic (vyper_to_abi_type env ty) /\
  vyper_decode_valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\
  dec (Tuple [vyper_to_abi_type env ty]) bs = ListV [av] /\
  abi_head_word bs <= LENGTH bs /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb (LENGTH bs) d
    (type_memory_bytes ce ty) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var (Lit 0w) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ fn_has_code st final func /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. val_in_memory tv v d t.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
    local_prefix ctx func (final.cs_current_bb,LENGTH final.cs_current_insts) initial t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_valid_singleton_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) initial = OK prepared` >>
  drule abi_valid_singleton_setup_live >> simp_tac bool_ss [FST, SND] >> strip_tac >>
  drule_all decoder_valid_singleton_child_input >> strip_tac >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all abi_decoder_valid_bytes_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready final) prepared = OK actual` >>
  `val_in_memory tv v d actual.vs_memory` by metis_tac[] >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule_all abi_decode_singleton_setup_shape >> strip_tac >>
  `inst_extends ready final` by
    (qpat_assum `isPREFIX ready.cs_current_insts final.cs_current_insts` mp_tac >>
     simp_tac std_ss [IS_PREFIX_APPEND, inst_extends_def, emitted_insts_def] >>
     strip_tac >> asm_rewrite_tac[] >> simp[DROP_LENGTH_APPEND]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `final.cs_current_bb = st.cs_current_bb` by metis_tac[] >>
  `final.cs_current_insts = st.cs_current_insts ++ emitted_insts st final` by
    metis_tac[inst_extends_def] >>
  `emitted_insts st final = emitted_insts st ready ++ emitted_insts ready final` by
    (irule emitted_insts_append >> metis_tac[inst_extends_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)` by fs[EVERY_CONJ] >>
  qpat_x_assum `emitted_insts st final = _` kall_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `LENGTH st.cs_current_insts + LENGTH (emitted_insts st final) =
    LENGTH final.cs_current_insts` by metis_tac[LENGTH_APPEND] >>
  `local_prefix ctx func (initial.vs_current_bb,
      initial.vs_inst_idx + LENGTH (emitted_insts st final)) initial
      (actual with vs_inst_idx := initial.vs_inst_idx + LENGTH (emitted_insts st final))` by
    (irule decoder_sequence_local_prefix >> asm_rewrite_tac[] >>
     qexists_tac `bb` >> asm_rewrite_tac[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qpat_x_assum `final.cs_current_insts = _` kall_tac >>
  qexists_tac `actual with vs_inst_idx := LENGTH final.cs_current_insts` >>
  qpat_x_assum `local_prefix _ _ _ _ _` mp_tac >>
  asm_simp_tac bool_ss [venom_state_accfupds, combinTheory.K_THM]
QED
