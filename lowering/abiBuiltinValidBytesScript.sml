(* Complete lower_abi_decode Bytes/String execution for all valid input windows.
   Actual setup, allocation and decoder execution are composed here. *)
Theory abiBuiltinValidBytes
Ancestors
  abiBuiltinValidBytesPre abiDecoderValidBytes abiBuiltinDecodeCode abiBuiltinDecodeSetup
  abiBuiltinSetupExecute abiBuiltinAllocationState abiDecoderBytes abiDecoderBytesTyped
  abiDecoderGuards abiDecoderContract abiDecoderReentry abiDecoderReentrySequence abiDecoderTypedCompose
  abiEncoder builtinAbi valueEncoding compileEnv emitHelperProps exprLoweringProps
  venomExecSemantics venomState finite_map words list rich_list arithmetic

Theorem abi_builtin_bytes_code:
  lower_abi_decode data (DecBytestring n) min_size max_size outsz st = (out,final) ==>
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends ready final` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`st`, `ready`, `final`] emitted_insts_append) >>
  impl_tac >- asm_simp_tac bool_ss [GSYM inst_extends_def] >> strip_tac >>
  drule_all inst_extends_trans >> simp[]
QED

Theorem lower_abi_decode_valid_bytes_sequence:
  lower_abi_decode data (DecBytestring n) min_size max_size
    (abi_decode_bytes_copy_size n) st = (out,final) /\
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand out actual = SOME (n2w d) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    actual.vs_allocas =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_allocas /\
    actual.vs_alloca_next =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_alloca_next /\
    fresh_vars_wrt final actual /\ actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_valid_bytes_ready >> strip_tac >>
  drule_all abi_decoder_valid_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready final) prepared = OK actual` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends ready final` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  qpat_assum `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  gvs[abi_decode_frame_def, Excl "dec_def", Excl "valid_enc_def"] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_VALID_BYTES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin valid bytes execution not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinValidBytes");
