(* Child metadata follows from validity and successful conversion, without a
   separate strict size-window check on the child's suffix. *)
Theory abiValidDecodedMetadata
Ancestors
  abiDecoderCoherence abiDecoderTypedContract vyperTypeABI vyperABI vyperValue contractABI
  compileEnv valueEncoding

Theorem abi_valid_decoded_metadata:
  abi_decoder_coherent ce env sf ty tv /\ valid_enc (vyper_to_abi_type env ty) bs /\
  abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v ==>
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec (vyper_to_abi_type env ty) bs) v
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  `has_type (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)` by
    (irule (cj 1 dec_has_type) >> first_assum ACCEPT_TAC) >>
  `value_has_type tv v` by
    (irule (cj 1 abi_to_vyper_well_typed) >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`dec (vyper_to_abi_type env ty) bs`, `env`, `ty`] >>
     asm_simp_tac bool_ss []) >>
  irule abi_decoder_coherent_root_metadata >> asm_simp_tac bool_ss [] >>
  qexists_tac `sf` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_DECODED_METADATA_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid decoded metadata not kernel closed: " ^ n)
  end) (DB.thms "abiValidDecodedMetadata");
