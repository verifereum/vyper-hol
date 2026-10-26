(* Snapshot-copy preservation used by bytestring and bulk-array decoding. *)
Theory abiDecoderCopy
Ancestors
  abiDecoderComposition abiDecoderContract emitHelperProps exprLoweringProps
  venomExecSemantics venomInst venomState compileEnv valueEncoding emitHelper

Theorem abi_decode_copy_vars:
  emit_void (abi_decode_copy_opcode opc) [dst;src;sz] st = ((),st') /\
  abi_decode_source_opcode opc /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  t.vs_vars = s.vs_vars
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  gvs[abi_decode_source_opcode_def, abi_decode_copy_opcode_def] >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def, mcopy_def,
      write_memory_with_expansion_def, AllCaseEqs()]
QED

Theorem abi_decode_copy_fresh:
  emit_void (abi_decode_copy_opcode opc) [dst;src;sz] st = ((),st') /\
  abi_decode_source_opcode opc /\
  run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st s ==>
  fresh_vars_wrt st' t
Proof
  strip_tac >> drule_all abi_decode_copy_vars >> strip_tac >>
  drule_all fresh_vars_wrt_emit_void >>
  simp[fresh_vars_wrt_def, lookup_var_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_COPY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder copy not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCopy");
