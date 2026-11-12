(* Local label compatibility from actual code embedding, not global freshness. *)
Theory exprSimAbiEncodeSeparation
Ancestors
  fragExec abiEncoderArrayLoopLayout abiDecoderLoopCode abiDecoderLoopEmit
  abiEncoderArrayHeader abiDecoderExecution compileEnv venomInst list rich_list

Theorem encode_emitted_label_compatible:
  fn_has_code sa sb func /\ MEM b (emitted_blocks sa sb) /\
  MEM c (emitted_blocks sa sb) /\ b.bb_label = c.bb_label ==> b = c
Proof
  simp[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem encode_final_label_compatible:
  fn_has_code sa sb func /\ MEM b (emitted_blocks sa sb) /\
  b.bb_label = sb.cs_current_bb ==> isPREFIX sb.cs_current_insts b.bb_instructions
Proof
  simp[fn_has_code_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem encode_final_label_separate:
  fn_has_code sa sb func /\ MEM b (emitted_blocks sa sb) /\
  ~isPREFIX sb.cs_current_insts b.bb_instructions ==> b.bb_label <> sb.cs_current_bb
Proof
  metis_tac[encode_final_label_compatible]
QED

Theorem encode_lookup_last_separate:
  lookup_block a blocks = SOME b /\ lookup_block c blocks = SOME d /\
  (LAST b.bb_instructions).inst_opcode <> (LAST d.bb_instructions).inst_opcode ==>
  a <> c
Proof
  metis_tac[optionTheory.SOME_11]
QED

Theorem encode_array_header_backedge_separate:
  abi_encode_array_header ip count_op owner = (labels,body_st) /\
  fn_has_code owner body_st func /\
  abi_decode_loop_suffix ip (Var iv) (FST labels) (SND (SND labels)) body_end = ((),exit_st) /\
  fn_has_code body_end exit_st func ==>
    FST labels <> body_end.cs_current_bb
Proof
  strip_tac >> drule_all abi_encode_array_header_code >> strip_tac >>
  drule_all abi_encode_array_suffix_code >> strip_tac >>
  irule encode_lookup_last_separate >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[abi_encode_array_header_insts_def, abi_decode_backedge_insts_def, LAST_APPEND,
       venomInstTheory.mk_inst_def]
QED

(* An empty exit prefix is genuinely compatible with an emitted block of
   the same label. This is a limitation of the suffix interface, not a
   counterexample to compilation of an actual whole encoder. *)
Theorem encode_suffix_empty_exit_alias:
  abi_decode_loop_suffix ip (Var iv) hdr st.cs_current_bb st = ((),final) ==>
  final.cs_current_bb = st.cs_current_bb /\ final.cs_current_insts = [] /\
  fn_has_code st final
    (fn with fn_blocks :=
      [<|bb_label := st.cs_current_bb; bb_instructions := st.cs_current_insts ++
        abi_decode_backedge_insts st.cs_next_id iv
          (STRING #"%" (toString st.cs_next_var)) ip hdr|>])
Proof
  simp[abi_decode_loop_suffix_shape, abi_decode_loop_suffix_state_def] >>
  strip_tac >> gvs[fn_has_code_def, emitted_blocks_def, lookup_block_def, FIND_thm]
QED
