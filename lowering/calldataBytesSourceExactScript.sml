(* Source-exact observations for padded calldata bytes and strings. *)
Theory calldataBytesSourceExact
Ancestors
  calldataBytesLive calldataBytesLeaf calldataSourceCorrespondence
  abiCanonicalHeadSize abiEncoderInputFrame abiDecoderString
  abiDecoderBytesTyped valueEncodingTyping valueEncodingDefs vyperCalldata
  vyperValue vyperTyping passSharedFrame venomExecSemantics venomState
  abiDecoderContract abiDecoderBytes abiEncoder compileEnv venomInst exprLoweringProps
  words arithmetic list rich_list

Theorem calldata_sequence_abort_empty[local]:
  !insts s a t.
    EVERY (\i. ~is_terminator i.inst_opcode) insts /\
    run_inst_seq insts s = Abort a t ==> t.vs_returndata = []
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  metis_tac[step_inst_base_abort_returndata]
QED

Theorem calldata_bytestring_source_outcome[local]:
  (tv = BaseTV (BytesT (Dynamic maxn)) \/ tv = BaseTV (StringT maxn)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) ==>
  ?t.
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (case cd_decode F s.vs_call_ctx.cc_calldata tv (w2n p) of
       NONE => run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
         t.vs_returndata = [] /\ t.vs_memory = s.vs_memory /\
         t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
     | SOME x => run_inst_seq (emitted_insts st st') s = OK t /\
         value_has_type tv x /\ val_wf tv x /\ val_in_memory tv x d t.vs_memory /\
         abi_decode_frame d (abi_decode_bytes_copy_size maxn) s t /\
         mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
           mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) s.vs_call_ctx.cc_calldata)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `maxn < dimword (:256)` by metis_tac[abi_decode_bytes_extent_capacity_bound] >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p s) <= maxn`
  >- (drule_all calldata_bytes_accepted_live >> strip_tac >>
      `32 + w2n (abi_decode_load CALLDATALOAD p s) <= abi_decode_bytes_copy_size maxn` by
        (mp_tac (cj 3 abi_decoder_bytes_copy_size |> Q.INST [`n` |-> `maxn`]) >> decide_tac) >>
      `mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p s)) t.vs_memory =
       mem_bytes_at (w2n p+32) (w2n (abi_decode_load CALLDATALOAD p s)) s.vs_call_ctx.cc_calldata` by
        (irule abi_encoder_window_slice >> goal_assum (drule_at Any) >> simp[]) >>
      qexists `t` >> simp[] >>
      qpat_x_assum `tv = _ \/ tv = _` strip_assume_tac >> gvs[] >>
      simp[cd_decode_def, GSYM calldata_decode_load_word] >>
      gvs[cd_bytes_def, mem_bytes_at_def, value_has_type_def, val_in_memory_def,
        abi_decoder_string_memory, n2w_w2n] >>
      irule (cj 1 value_has_type_val_wf) >> simp[value_has_type_def]) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p s)` by decide_tac >>
  drule_all calldata_bytes_rejected_live >> strip_tac >>
  `t.vs_returndata = []` by
    (irule calldata_sequence_abort_empty >> goal_assum (drule_at Any) >>
     drule calldata_bytes_opcodes >> simp[EVERY_MEM] >> metis_tac[]) >>
  qexists `t` >> simp[] >>
  qpat_x_assum `tv = _ \/ tv = _` strip_assume_tac >> gvs[] >>
  simp[cd_decode_def, GSYM calldata_decode_load_word]
QED

Theorem calldata_bytes_source_outcome:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) ==>
  ?t.
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (case cd_decode F s.vs_call_ctx.cc_calldata (BaseTV (BytesT (Dynamic maxn))) (w2n p) of
       NONE => run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
         t.vs_returndata = [] /\ t.vs_memory = s.vs_memory /\
         t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
     | SOME x => run_inst_seq (emitted_insts st st') s = OK t /\
         value_has_type (BaseTV (BytesT (Dynamic maxn))) x /\
         val_wf (BaseTV (BytesT (Dynamic maxn))) x /\
         val_in_memory (BaseTV (BytesT (Dynamic maxn))) x d t.vs_memory /\
         abi_decode_frame d (abi_decode_bytes_copy_size maxn) s t /\
         mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
           mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) s.vs_call_ctx.cc_calldata)
Proof
  strip_tac >> irule calldata_bytestring_source_outcome >>
  simp[] >> qexistsl [`dst`, `src`] >> simp[]
QED

Theorem calldata_string_source_outcome:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) ==>
  ?t.
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (case cd_decode F s.vs_call_ctx.cc_calldata (BaseTV (StringT maxn)) (w2n p) of
       NONE => run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
         t.vs_returndata = [] /\ t.vs_memory = s.vs_memory /\
         t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section
     | SOME x => run_inst_seq (emitted_insts st st') s = OK t /\
         value_has_type (BaseTV (StringT maxn)) x /\
         val_wf (BaseTV (StringT maxn)) x /\
         val_in_memory (BaseTV (StringT maxn)) x d t.vs_memory /\
         abi_decode_frame d (abi_decode_bytes_copy_size maxn) s t /\
         mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
           mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) s.vs_call_ctx.cc_calldata)
Proof
  strip_tac >> irule calldata_bytestring_source_outcome >>
  simp[] >> qexistsl [`dst`, `src`] >> simp[]
QED
