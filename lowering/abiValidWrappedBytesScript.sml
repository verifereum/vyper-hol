(* Execute the actual dynamic singleton constructor from valid ABI bytes. *)
Theory abiValidWrappedBytes
Ancestors
  abiValidWrappedBytesInput abiDecoderValidBytes abiDecoderWrappedBytes
  abiDecoderWrappedBytesFragment abiDecoderSingletonSetup abiDecoderBytes abiDecoderBytesTyped
  abiDecoderTypedCompose abiDecoderGuards abiDecoderContract abiDecoderReentrySequence
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding
  venomExecSemantics venomState venomInst words list rich_list

Theorem abi_valid_wrapped_bytes_sequence:
  compile_abi_decode_to_buf dst src MLOAD hi
    (DecComplex T [(DecBytestring n,32,mem_sz)]) st = ((),st') /\
  abi_valid_wrapped_bytes_pre n at bs payload st src dst hi sb d s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d t.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d t.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    fresh_vars_wrt st' t /\ t.vs_halted = s.vs_halted /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_wrapped_bytes_phases, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = (child_ops,c1)` >>
  PairCases_on `child_ops` >> gvs[] >>
  rename1 `abi_decode_singleton_setup dst src MLOAD hi st = ((child_src,child_dst),c1)` >>
  `compile_abi_decode_to_buf child_dst child_src MLOAD hi (DecBytestring n) c1 =
    ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >> asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_valid_wrapped_bytes_setup >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK mid` >>
  drule_all abi_decoder_valid_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') mid = OK t` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends c1 st'` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac bool_ss [] >>
  gvs[abi_decode_frame_def, Excl "dec_def", Excl "valid_enc_def"] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_WRAPPED_BYTES_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid wrapped bytes execution not kernel closed: " ^ n)
  end) (DB.thms "abiValidWrappedBytes");
