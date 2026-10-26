(* Execute an actual translated encoder followed by the builtin length store.
   TOP-LEVEL: abi_scratch_builtin_body_finish keeps the optional method prefix
   and composes one physical effect for the complete used output buffer. *)
Theory abiScratchBuiltinBody
Ancestors
  abiScratchBuiltinCompose abiScratchEncoderRecursive abiScratchEncoderRun abiScratchEncoderContract
  abiBuiltinEncodeCode abiEncoderAppend abiEncoderCounters abiDecoderAppend abiDecoderAllocation
  abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderContract abiDecoderLoop
  fragExec compileEnv exprLowering valueEncoding contractABI venomState words list arithmetic

Theorem abi_scratch_builtin_body_finish:
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) ready = (len_op,body_end) /\
  abi_builtin_encode_finish buf len_op mid_size body_end = ((),final) /\
  fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input (type_to_abi_enc_info sf ce ty) at av ready src dst sb source_cap
    (p+32+mid_size) (LENGTH (enc at av)) first last b cap initial /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  abi_footprint_disjoint p (32+mid_size+LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ first <= ready.cs_next_id /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = ready.cs_current_bb /\
  initial.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)+mid_size) /\
    mem_bytes_at (p+32+mid_size) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends body_end final` by (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`ready`, `body_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_encoder (type_to_abi_enc_info sf ce ty)` by simp[abi_scratch_encoder_translation] >>
  `body_end.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_id <= last /\
   body_end.cs_next_id <= final.cs_next_id` by (Cases_on `mid_size > 0` >> gvs[] >> decide_tac) >>
  qpat_assum `final.cs_blocks = body_end.cs_blocks` (fn blocks =>
    qpat_assum `final.cs_current_bb = body_end.cs_current_bb` (fn label =>
    qpat_assum `ready.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [blocks,label]))) >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `body_end`, `out` |-> `len_op`,
    `d` |-> `p+32+mid_size:num`, `ctx` |-> `ctx`,
    `ei` |-> `type_to_abi_enc_info sf ce ty`] abi_scratch_encoder_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  `p < dimword (:256)` by
    (qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >> decide_tac) >>
  mp_tac (Q.INST [`encoded_len` |-> `len_op`, `len` |-> `LENGTH (enc at av)`,
    `bytes` |-> `enc at av`] abi_scratch_builtin_compose) >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_BUILTIN_BODY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI scratch builtin recursive body not kernel closed: " ^ n)
  end) (DB.thms "abiScratchBuiltinBody");
