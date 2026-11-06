Theory exprSimAbiEncodeTupleOpen
Ancestors
  abiEncoderOpenRelocate abiEncoderOpenInput abiEncoderWrites abiEncoderBytes
  abiDecoderContract abiDecoderReentry abiTupleEncodeSlot
  context exprLowering emitHelper emitHelperProps exprLoweringProps
  valueEncoding valueEncodingProps compileEnv venomState venomInst venomMemDefs
  contractABI words list

(* Only the meaningful prefix is owned. MCOPY may snapshot unused source
   padding that overlaps the destination, without affecting this result. *)
Theorem abi_encode_open_copy_write:
  compile_copy_memory dst src n st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  n < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_encoder_open_input ei at av sb cap s.vs_memory /\ cap <= n ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\
    inst_extends st final /\
    abi_encoder_open_input ei at av d n actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d n s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op. eval_operand op actual = eval_operand op s)
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      `abi_encoder_open_input ei at av d 0 s.vs_memory` by
        (irule abi_encoder_open_input_relocate_capacity >>
         goal_assum (drule_at Any) >> simp[mem_bytes_at_def]) >>
      qexists_tac `s` >>
      simp[emitted_insts_def, run_inst_seq_def, inst_extends_def,
           abi_decode_frame_def]) >>
  `emit_void MCOPY [dst;src;Lit (n2w n)] st = ((),final)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all abi_encoder_emit_copy >> strip_tac >>
  `abi_decode_frame d n s (mcopy d sb n s)` by
    (simp_tac bool_ss [abi_decode_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> simp[]) >> simp[]) >>
  drule_all abi_encoder_open_input_mcopy_prefix >>
  disch_then (qspec_then `d` assume_tac) >>
  qexists_tac `mcopy d sb n s` >> simp[abi_encoder_copy_eval]
QED

Theorem abi_encode_open_bytes_copy:
  compile_copy_memory dst src n st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  n < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
  LENGTH bs <= maxlen /\ 32 + LENGTH bs <= n /\
  mem_word_at sb s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (sb+32) (LENGTH bs) s.vs_memory = bs ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\
    abi_encoder_open_input (AbiBytestring maxlen) at (BytesV bs)
      d n actual.vs_memory /\ abi_decode_frame d n s actual
Proof
  strip_tac >>
  `abi_encoder_open_input (AbiBytestring maxlen) at (BytesV bs)
     sb (32+LENGTH bs) s.vs_memory` by
    (irule abiEncoderOpenInputTheory.bytes >> simp[]) >>
  drule_all abi_encode_open_copy_write >> metis_tac[]
QED

(* The destination starts precisely where the meaningful prefix ends,
   inside the unused half of the declared source capacity. *)
Theorem abi_encode_open_copy_padding_overlap:
  abi_encoder_open_input (AbiBytestring 32) (Bytes NONE) (BytesV [])
    0 32 s.vs_memory ==>
  abi_encoder_open_input (AbiBytestring 32) (Bytes NONE) (BytesV [])
    32 64 (mcopy 32 0 64 s).vs_memory /\
  venomMemDefs$regions_disjoint (0,32) (32,64) /\
  ~venomMemDefs$regions_disjoint (0,64) (32,64)
Proof
  strip_tac >> reverse conj_tac
  >- simp[venomMemDefsTheory.regions_disjoint_def] >>
  irule abi_encoder_open_input_mcopy_prefix >>
  goal_assum (drule_at Any) >> simp[]
QED
