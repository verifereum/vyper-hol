(* Coherent closure of same-endpoint counted physical ABI decoding. *)
Theory bodyIntCallDecoderCountedClosure
Ancestors
  bodyIntCallDecoderCountedLeaves bodyIntCallDecoderCountedAggregates
  bodyIntCallDecoderCountedArray bodyIntCallDecoderCountedContract
  abiDecoderOffsetHead abiDecoderCoherence abiScratchDecoderContract
  abiScratchEncoderContract abiDecoderAllocation abiDecoderContract abiEncoder
  fragGasPath fragExec compileEnv valueEncoding venomState vyperAST vyperValue

Theorem intcall_scratch_decoder_counted_evaluated_array:
  intcall_scratch_decoder_counted ce env sf ty tv /\
  evaluate_type env (ArrayT ty bound) = SOME (ArrayTV tv bound) ==>
  intcall_scratch_decoder_counted ce env sf (ArrayT ty bound) (ArrayTV tv bound)
Proof
  strip_tac >> drule abi_decoder_evaluated_array_head >> disch_then assume_tac >>
  Cases_on `bound`
  >- (irule intcall_scratch_decoder_counted_fixed_array >> asm_simp_tac bool_ss []) >>
  irule intcall_scratch_decoder_array >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_decoder_counted_coherent:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
    intcall_scratch_decoder_counted ce env sf ty tv
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- simp[intcall_scratch_decoder_counted_base]
  >- simp[intcall_scratch_decoder_counted_flag]
  >- (rpt strip_tac >>
      rename1 `abi_decoder_header ce env (ArrayT elem bound) (ArrayTV elem_tv bound)` >>
      `evaluate_type env (ArrayT elem bound) = SOME (ArrayTV elem_tv bound)` by
        fs[abi_decoder_header_def] >>
      irule intcall_scratch_decoder_counted_evaluated_array >> asm_simp_tac bool_ss [])
  >- (rpt strip_tac >> irule intcall_scratch_decoder_counted_tuple >> asm_simp_tac bool_ss []) >>
  rpt strip_tac >> irule intcall_scratch_decoder_counted_struct >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_decoder_decode:
  compile_abi_decode_to_buf dst src opc base_op hi (type_to_abi_dec_info sf ce ty) start = ((),end_st) /\
  (base_op = Lit 0w \/ opc = MLOAD) /\ fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder_input ce env sf ty tv bs v start src dst opc base_op hi B sb d
    first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor start /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual n. val_in_memory tv v d actual.vs_memory /\
    abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_scratch_decoder_input_def] >>
  drule intcall_scratch_decoder_counted_coherent >>
  disch_then (drule_all o PURE_REWRITE_RULE [intcall_scratch_decoder_counted_def]) >>
  simp_tac bool_ss []
QED
