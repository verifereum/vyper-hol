(* Concrete malformed dynamic return-data probe; not an extcall counterexample. *)
Theory abiDecoderWrapProbe
Ancestors
  abiDecoderReject abiDecoderRejectResources abiDecoderFrame vyperABI builtinAbi abiEncoder
  fragGasSeq fragGasMode venomExecSemantics venomState compileEnv words list finite_map

Definition wrap_probe_bytes_def:
  wrap_probe_bytes = REPLICATE 31 (255w:word8) ++ [96w]
End

Definition wrap_probe_start_def:
  wrap_probe_start =
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>
End

Definition wrap_probe_state_def:
  wrap_probe_state = (init_venom_state "entry") with
    vs_memory := REPLICATE 128 0w ++ wrap_probe_bytes
End

Definition wrap_probe_compile_def:
  wrap_probe_compile = compile_abi_decode_to_buf
    (Lit 256w) (Lit 128w) MLOAD (Lit 160w)
    (DecComplex T [(DecBytestring 32,32,64)]) wrap_probe_start
End

Theorem wrap_probe_source_rejects:
  LENGTH wrap_probe_bytes = 32 /\
  evaluate_abi_decode_return FEMPTY (BaseT (BytesT (Dynamic 32)))
    wrap_probe_bytes = INR "abi_decode invalid"
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED

Theorem wrap_probe_arithmetic:
  (128w:bytes32) + -160w = -32w /\
  ~((-32w:bytes32) <+ 128w) /\
  (-32w:bytes32) + 32w = 0w /\
  mload (dimword(:256) - 32) wrap_probe_state = 0w
Proof
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED

Theorem wrap_probe_decoder_finishes:
  ?t. run_inst_seq
    (emitted_insts wrap_probe_start (SND wrap_probe_compile))
    wrap_probe_state = OK t
Proof
  EVAL_TAC >> CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

Theorem wrap_probe_descriptor:
  type_to_abi_dec_info FEMPTY ce (TupleT [BaseT (BytesT (Dynamic 32))]) =
    DecComplex T [(DecBytestring 32,32,64)]
Proof
  EVAL_TAC
QED

Theorem wrap_probe_input:
  abi_reject_input (Lit 128w) (Lit 160w) 128 wrap_probe_bytes
    [(256,64)] wrap_probe_state /\
  fresh_vars_wrt wrap_probe_start wrap_probe_state /\
  ~wrap_probe_state.vs_halted
Proof
  simp[abi_reject_input_def, wrap_probe_state_def, wrap_probe_start_def,
       fresh_vars_wrt_def, init_venom_state_def, eval_operand_def,
       abi_footprint_disjoint_def] >>
  EVAL_TAC >> CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >> EVAL_TAC
QED

Theorem wrap_probe_decoder_path:
  lookup_block wrap_probe_state.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts wrap_probe_start (SND wrap_probe_compile))
    (DROP wrap_probe_state.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_marked_path F ctx func wrap_probe_state 0 (OK t)
Proof
  rpt strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts wrap_probe_start (SND wrap_probe_compile)) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS)
      (emitted_insts wrap_probe_start (SND wrap_probe_compile))) = 0` by EVAL_TAC >>
  mp_tac wrap_probe_decoder_finishes >> strip_tac >>
  `~wrap_probe_state.vs_halted` by metis_tac[wrap_probe_input] >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[gas_marked_path_def] >> metis_tac[]
QED

Theorem wrap_probe_decoder_mismatch:
  evaluate_abi_decode_return FEMPTY (BaseT (BytesT (Dynamic 32)))
    wrap_probe_bytes = INR "abi_decode invalid" /\
  (?t. run_inst_seq (emitted_insts wrap_probe_start (SND wrap_probe_compile))
     wrap_probe_state = OK t) /\
  ~(?a t. run_inst_seq (emitted_insts wrap_probe_start (SND wrap_probe_compile))
     wrap_probe_state = Abort a t)
Proof
  mp_tac wrap_probe_source_rejects >>
  mp_tac wrap_probe_decoder_finishes >> rpt strip_tac >> gvs[] >> metis_tac[]
QED
