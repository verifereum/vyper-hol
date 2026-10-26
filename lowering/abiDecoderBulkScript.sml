(* Successful execution of the emitted static-element dynamic-array decoder. *)
Theory abiDecoderBulk
Ancestors
  abiDecoderDynarrayPrefix abiDecoderBulkBody abiDecoderArrayHeader
  abiDecoderBulkPayload abiDecoderDynarrayBound abiDecoderGuardLE
  abiDecoderGuards abiDecoderContract abiDecoderComposition abiEncoder
  emitHelper compileEnv valueEncoding venomExecSemantics venomState words

Theorem abi_decode_bulk_phases:
  abi_decode_source_opcode opc /\ ~dec_info_needs_clamp ei ==>
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) =
    do abi_decode_dynarray_prefix src opc hi maxn abi_sz;
       abi_decode_bulk_body dst src opc mem_sz
    od
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, compile_abi_decode_to_buf_def,
       abi_decode_dynarray_prefix_def, abi_decode_count_guard_def,
       abi_decode_dynarray_end_guard_def, abi_decode_dynarray_end_def,
       abi_decode_le_guard_def, abi_decode_bulk_body_def,
       abi_decode_array_header_def, abi_decode_bulk_payload_def,
       abi_decode_copy_opcode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bulk_sequence:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  (opc = MLOAD ==> sb + 32 + n * mem_sz <= d \/ d + 32 <= sb + 32) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s) /\
    abi_decode_frame d (32 + n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases, comp_ignore_bind_def,
                       comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_dynarray_prefix src opc hi maxn abi_sz st = (prefix_result,c1)` >>
  Cases_on `prefix_result` >>
  mp_tac (Q.INST [`st'` |-> `c1`] abi_decode_dynarray_prefix_sequence) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb) /\
   eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `abi_decode_load opc (n2w sb : bytes32) s1 = n2w n` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  `abi_decode_bulk_body dst src opc mem_sz c1 = ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >>
     asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decode_bulk_body_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[abi_decode_frame_def, abi_decode_source_def] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder bulk execution not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulk");
