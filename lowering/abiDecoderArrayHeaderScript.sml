(* The decoder reloads and writes the dynamic-array count before its payload. *)
Theory abiDecoderArrayHeader
Ancestors
  abiDecoderContract abiDecoderGuards emitHelperProps exprLoweringProps
  valueEncoding valueEncodingProps compileEnv emitHelper venomExecSemantics venomState words

Theorem abi_decode_mstore_frame:
  abi_decode_frame d 32 s (mstore d w s)
Proof
  simp[abi_decode_frame_def] >> conj_tac
  >- (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Definition abi_decode_array_header_def:
  abi_decode_array_header dst src opc =
    do cnt <- emit_op opc [src];
       emit_void MSTORE [dst;cnt];
       return cnt
    od
End

Theorem abi_decode_array_header_sequence:
  abi_decode_array_header dst src opc st = (cnt,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand cnt t = SOME (abi_decode_load opc p s) /\
    mem_word_at d t.vs_memory = abi_decode_load opc p s /\
    abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op opc [src] st = (cnt,c1)` >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  drule_all emit_void_MSTORE_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  assume_tac (Q.INST [`s` |-> `s1`, `w` |-> `abi_decode_load opc (p:bytes32) s`]
    abi_decode_mstore_frame) >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[w2n_n2w, eval_operand_mstore, mstore_mem_word_at_same,
      abi_decode_frame_def] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_ARRAY_HEADER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder array header not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderArrayHeader");
