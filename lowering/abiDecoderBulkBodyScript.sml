(* Count/header and payload writes in the static-element dynamic-array path. *)
Theory abiDecoderBulkBody
Ancestors
  abiDecoderArrayHeader abiDecoderBulkPayload abiDecoderFrameCompose
  abiDecoderContract abiDecoderGuards compileEnv emitHelper valueEncoding
  venomExecSemantics venomState words arithmetic

Definition abi_decode_bulk_body_def:
  abi_decode_bulk_body dst src opc mem_sz =
    do cnt <- abi_decode_array_header dst src opc;
       abi_decode_bulk_payload dst src cnt mem_sz opc
    od
End

Theorem abi_decode_bulk_body_sequence:
  abi_decode_bulk_body dst src opc mem_sz st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w n /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  (opc = MLOAD ==> sb + 32 + n * mem_sz <= d \/ d + 32 <= sb + 32) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s) /\
    abi_decode_frame d (32 + n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst src opc st = (cnt,c1)` >>
  `d < dimword (:256)` by decide_tac >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb) /\
   eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `c1`, `s` |-> `s1`]
    abi_decode_bulk_payload_sequence) >> impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `mem_word_at d t.vs_memory = mem_word_at d s1.vs_memory` by
    (irule abi_decode_frame_mem_word >>
     qexistsl_tac [`d + 32`, `n * mem_sz`] >> simp[]) >>
  `mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s1) =
   mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s)` by
    (irule abi_decode_frame_source_window >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`d`, `32`] >> simp[]) >>
  `abi_decode_frame d (32 + n * mem_sz) s t` by
    (irule abi_decode_frame_adjacent >> qexists_tac `s1` >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_BULK_BODY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder bulk body not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderBulkBody");
