(* Tuple decoding composes the actual guard and heterogeneous member decoders. *)
Theory abiDecoderCorrectTuple
Ancestors
  abiDecoderCorrect abiDecoderTupleInputs abiDecoderComplexExecute abiDecoderMemberInfos
  abiDecoderEffect abiDecoderCoherence abiDecoderReentry abiDecoderTypedContract
  abiDecoderContract fragExec compileEnv valueEncoding valueEncodingProps
  vyperABI venomState words list

Theorem abi_decoder_correct_tuple:
  LIST_REL (abi_decoder_correct ce env sf) tys tvs ==>
  abi_decoder_correct ce env sf (TupleT tys) (TupleTV tvs)
Proof
  strip_tac >> simp_tac bool_ss [abi_decoder_correct_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_tuple_inputs >> strip_tac >> gvs[Excl "enc_def"] >>
  (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_decoder_tuple_infos]) >>
  mp_tac (Q.INST [`st` |-> `start`, `final` |-> `end_st`,
    `dyn` |-> `EXISTS (is_abi_dynamic ce.ce_struct_fields) tys`] abi_decoder_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [val_in_memory_tuple])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CORRECT_TUPLE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple correctness not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCorrectTuple");
