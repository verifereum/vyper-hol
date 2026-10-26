(* Source type coherence for either actual singleton-wrapping choice. *)
Theory abiDecoderValidWrapping
Ancestors
  abiCallerWrapped abiDecoderCallerChecks abiDecoderCoherence abiDecoderReadableTypes
  abiBoundaryChecks compileEnv valueEncoding vyperABI vyperValue list

Theorem abi_decoder_coherent_singleton:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_coherent ce env sf (TupleT [ty]) (TupleTV [tv])
Proof
  strip_tac >> drule abi_decoder_coherent_header >> strip_tac >>
  `evaluate_type env ty = SOME tv` by fs[abi_decoder_header_def] >>
  drule abi_caller_singleton_type >> strip_tac >>
  irule decoder_caller_singleton >> asm_simp_tac bool_ss []
QED

Theorem abi_decoder_valid_wrapping:
  abi_decoder_coherent ce env sf ty tv ==>
  abi_decoder_coherent ce env sf (if wrapped then TupleT [ty] else ty)
    (if wrapped then TupleTV [tv] else tv)
Proof
  strip_tac >> Cases_on `wrapped` >> simp[abi_decoder_coherent_singleton]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_WRAPPING_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI source-valid wrapping fact not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidWrapping");
