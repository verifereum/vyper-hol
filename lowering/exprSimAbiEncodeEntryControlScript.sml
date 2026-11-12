(* Original-entry aliases are tested against actual emitted loop code. *)
Theory exprSimAbiEncodeEntryControl
Ancestors
  exprSimAbiEncodeSeparation exprSimAbiEncodeLabelProvenance
  abiEncoderArrayLoopLayout abiEncoderArrayCode abiEncoderArrayHeader
  abiDecoderLoopEmit abiDecoderLoopCode abiDecoderDynamicLoopSetup abiDecoderExecution
  abiEncoder emitHelper fragExec compileEnv venomInst venomWf
  list rich_list arithmetic
Libs monadsyntax

Theorem encode_array_owner_header_separate:
  abi_encode_array_header ip count_op owner = (labels,body_st) /\
  fn_has_code owner body_st func ==> owner.cs_current_bb <> FST labels
Proof
  strip_tac >> drule_all abi_encode_array_header_code >> strip_tac >>
  irule encode_lookup_last_separate >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[abi_encode_array_header_insts_def, LAST_APPEND, mk_inst_def]
QED

(* A retained prefix can coincide with the three real static exit instructions.
   The compiler counters need not be fresh for instructions already retained. *)
Definition enc_entry_exit_prefix_def:
  enc_entry_exit_prefix =
    [mk_inst 17 MLOAD [Lit 0w] ["%12"];
     mk_inst 18 MUL [Var "%12"; Lit 32w] ["%13"];
     mk_inst 19 ADD [Lit 32w; Var "%13"] ["%14"]]
End

Definition enc_entry_alias_owner_def:
  enc_entry_alias_owner st = st with
    <|cs_next_var := 0; cs_next_id := 0; cs_next_label := 0;
      cs_blocks := []; cs_current_bb := fresh_label_output "enc_dyn_exit" 2;
      cs_current_insts := enc_entry_exit_prefix|>
End

Definition enc_entry_alias_loop_def:
  enc_entry_alias_loop =
    do labels <- abi_encode_array_header (Lit 0w) (Lit 1w);
       idx <- abi_encode_array_static_body (Lit 0w) (Lit 0w) (Lit 32w) AbiPrimWord 32 32;
       abi_decode_loop_suffix (Lit 0w) idx (FST labels) (SND (SND labels));
       abi_encode_array_static_exit (Lit 0w) 32
    od
End

Definition enc_entry_alias_final_def:
  enc_entry_alias_final st = SND (enc_entry_alias_loop (enc_entry_alias_owner st))
End

Theorem encode_entry_exit_alias_position:
  (enc_entry_alias_final st).cs_current_bb = (enc_entry_alias_owner st).cs_current_bb /\
  (enc_entry_alias_final st).cs_current_insts = enc_entry_exit_prefix /\
  LENGTH (enc_entry_alias_owner st).cs_current_insts = 3
Proof
  simp[enc_entry_alias_final_def, enc_entry_alias_loop_def,
    enc_entry_alias_owner_def, enc_entry_exit_prefix_def,
    abi_encode_array_header_def, abi_encode_array_static_body_def,
    abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
    abi_decode_indexed_coordinates_def, compile_abi_encode_static_info_def,
    compile_abi_encode_static_def, abi_decode_loop_suffix_def,
    abi_encode_array_static_exit_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_label_def, new_block_def, emit_op_def,
    emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def,
    fresh_label_output_def] >> EVAL_TAC
QED

Definition enc_entry_alias_func_def:
  enc_entry_alias_func st fn = fn with fn_blocks :=
    emitted_blocks (enc_entry_alias_owner st) (enc_entry_alias_final st)
End

Definition enc_entry_alias_blocks_def:
  enc_entry_alias_blocks = (enc_entry_alias_final ARB).cs_blocks
End

Theorem encode_entry_exit_alias_blocks:
  (enc_entry_alias_final st).cs_blocks = enc_entry_alias_blocks
Proof
  simp[enc_entry_alias_blocks_def, enc_entry_alias_final_def, enc_entry_alias_loop_def,
    enc_entry_alias_owner_def, abi_encode_array_header_def, abi_encode_array_static_body_def,
    abi_encode_array_addresses_def, abi_decode_array_head_setup_def,
    abi_decode_indexed_coordinates_def, compile_abi_encode_static_info_def,
    compile_abi_encode_static_def, abi_decode_loop_suffix_def,
    abi_encode_array_static_exit_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, fresh_label_def, new_block_def, emit_op_def,
    emit_void_def, emit_inst_def, fresh_var_def, fresh_id_def, emit_def]
QED

Theorem encode_entry_exit_alias_embedding:
  fn_has_code (enc_entry_alias_owner st) (enc_entry_alias_final st)
    (enc_entry_alias_func st fn) /\
  fn_inst_ids_distinct (enc_entry_alias_func st fn)
Proof
  simp[enc_entry_alias_func_def, fn_has_code_def, emitted_blocks_def,
    encode_entry_exit_alias_position, encode_entry_exit_alias_blocks,
    enc_entry_alias_owner_def, fn_inst_ids_distinct_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem encode_entry_exit_alias_lookup:
  lookup_block (enc_entry_alias_owner st).cs_current_bb
    (enc_entry_alias_func st fn).fn_blocks = SOME
      <|bb_label := (enc_entry_alias_owner st).cs_current_bb;
        bb_instructions := enc_entry_exit_prefix ++
          [mk_inst 0 JMP [Label (fresh_label_output "enc_dyn_hdr" 0)] []]|>
Proof
  simp[enc_entry_alias_func_def, emitted_blocks_def,
    encode_entry_exit_alias_blocks, enc_entry_alias_owner_def] >> EVAL_TAC
QED

Theorem encode_entry_exit_alias_cut:
  ((enc_entry_alias_owner st).cs_current_bb,
    LENGTH (enc_entry_alias_owner st).cs_current_insts) =
  ((enc_entry_alias_final st).cs_current_bb,
    LENGTH (enc_entry_alias_final st).cs_current_insts) /\
  (!bb. lookup_block (enc_entry_alias_owner st).cs_current_bb
      (enc_entry_alias_func st fn).fn_blocks = SOME bb ==>
    get_instruction bb 3 = SOME
      (mk_inst 0 JMP [Label (fresh_label_output "enc_dyn_hdr" 0)] []))
Proof
  conj_tac
  >- simp[encode_entry_exit_alias_position, enc_entry_exit_prefix_def] >>
  rpt strip_tac >>
  gvs[encode_entry_exit_alias_lookup, enc_entry_exit_prefix_def, get_instruction_def]
QED

Theorem encode_lookup_last_id_equal:
  lookup_block a blocks = SOME b /\ lookup_block a blocks = SOME c ==>
  (LAST b.bb_instructions).inst_id = (LAST c.bb_instructions).inst_id
Proof
  metis_tac[optionTheory.SOME_11]
QED

Theorem encode_array_owner_backedge_alias_id:
  abi_encode_array_header ip count_op owner = (labels,body_st) /\
  fn_has_code owner body_st func /\
  abi_decode_loop_suffix ip (Var iv) (FST labels) (SND (SND labels))
    body_end = ((),exit_st) /\
  fn_has_code body_end exit_st func /\
  owner.cs_current_bb = body_end.cs_current_bb ==>
  owner.cs_next_id = body_end.cs_next_id + 2
Proof
  strip_tac >> drule_all abi_encode_array_header_code >> strip_tac >>
  drule_all abi_encode_array_suffix_code >> strip_tac >>
  qpat_x_assum `lookup_block (FST labels) _ = _` kall_tac >>
  qpat_x_assum `lookup_block owner.cs_current_bb _ = _`
    (mp_then Any mp_tac encode_lookup_last_id_equal) >>
  simp[LAST_APPEND, abi_decode_backedge_insts_def, mk_inst_def]
QED
