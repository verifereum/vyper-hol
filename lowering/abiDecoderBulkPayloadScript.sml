(* The actual static-element dynamic-array payload-copy block. *)
Theory abiDecoderBulkPayload
Ancestors
  abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderCopy abiDecoderComposition
  abiDecoderContract abiDecoderGuards emitHelperProps exprLoweringProps compileEnv
  emitHelper valueEncoding venomExecSemantics venomState words

Definition abi_decode_bulk_payload_def:
  abi_decode_bulk_payload dst src cnt mem_sz opc =
    do copy_sz <- emit_op MUL [cnt; Lit (n2w mem_sz)];
       src_data <- emit_op ADD [src; Lit 32w];
       dst_data <- emit_op ADD [dst; Lit 32w];
       emit_void (abi_decode_copy_opcode opc) [dst_data;src_data;copy_sz]
    od
End

Theorem abi_decode_bulk_payload_sequence:
  abi_decode_bulk_payload dst src cnt mem_sz opc st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand cnt s = SOME (n2w n) /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s) /\
    abi_decode_frame (d + 32) (n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp[abi_decode_bulk_payload_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
  rename1 `emit_op ADD [dst; Lit 32w] c2 = (dst_data,c3)` >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >> gvs[word_mul_n2w] >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  qspecl_then [`dst`, `Lit 32w`, `n2w d`, `32w`, `c2`, `dst_data`, `c3`, `s2`]
    mp_tac abi_decode_add_sequence >>
  impl_tac >- simp[eval_operand_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `eval_operand sz_op s3 = SOME (n2w (n * mem_sz)) /\
   eval_operand src_data s3 = SOME ((n2w sb : bytes32) + 32w)` by
    (ONCE_REWRITE_TAC [arithmeticTheory.MULT_COMM] >> metis_tac[]) >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 st') s3 = OK t` >>
  `fresh_vars_wrt st' t` by (drule_all abi_decode_copy_fresh >> simp[]) >>
  drule inst_extends_emit_void >> strip_tac >>
  `run_inst_seq (emitted_insts c2 st') s2 = OK t /\ inst_extends c2 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`, `c3`] >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 = OK t /\ inst_extends c1 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[word_add_n2w, w2n_n2w, abi_decode_copy_bytes_def,
    mem_bytes_at_def, abi_decode_source_def, abi_decode_frame_def] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_PAYLOAD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder bulk payload not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulkPayload");
