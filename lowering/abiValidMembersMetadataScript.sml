(* Source conversion establishes member metadata for actual noncanonical bytes. *)
Theory abiValidMembersMetadata
Ancestors
  abiValidMembers abiDecoderMembers abiDecoderCoherence abiDecoderTypedContract
  abiDecodeRanges vyperTypeABI vyperTypeDefaults vyperABIValid vyperABI vyperValue
  contractABI compileEnv valueEncoding list

Theorem abi_valid_members_metadata:
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  valid_enc_tuple (MAP (vyper_to_abi_type env) tys) raw_bytes hds /\
  abi_to_vyper_list env tys (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw_bytes hds) = SOME vs ==>
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) raw_bytes hds) vs
Proof
  strip_tac >> drule abi_valid_members_view >> strip_tac >>
  `LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs` by
    (irule LIST_REL_mono >> qexists_tac `abi_decoder_coherent ce env sf` >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     drule abi_decoder_coherent_header >> simp[abi_decoder_header_def]) >>
  drule_all (cj 2 abi_to_vyper_well_typed) >> strip_tac >>
  irule abi_decoder_members_intro >>
  fs[values_have_types_LIST_REL, Excl "valid_enc_def", Excl "dec_def", Excl "enc_def"]
QED

Theorem abi_valid_tuple_source_values:
  evaluate_abi_decode env (TupleT tys) bs = INL (ArrayV (TupleV vs)) ==>
  valid_enc (Tuple (MAP (vyper_to_abi_type env) tys)) bs /\
  valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  abi_to_vyper_list env tys
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) = SOME vs /\
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= LENGTH bs
Proof
  strip_tac >>
  `valid_enc (Tuple (MAP (vyper_to_abi_type env) tys)) bs` by
    (drule evaluate_abi_decode_vyper_valid_enc >>
     simp[vyper_valid_enc_def, vyper_to_abi_types_MAP, Excl "valid_enc_def", Excl "dec_def"]) >>
  drule abi_valid_tuple_view >> strip_tac >>
  gvs[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
      vyper_to_abi_types_MAP, Once abi_to_vyper_def, Once valid_enc_def,
      AllCaseEqs(), Excl "valid_enc_def", Excl "dec_def"] >>
  simp[Once valid_enc_def]
QED

Theorem abi_valid_tuple_source_members:
  abi_decoder_coherent ce env sf (TupleT tys) (TupleTV tvs) /\
  evaluate_abi_decode env (TupleT tys) bs = INL (ArrayV (TupleV vs)) ==>
  abi_decoder_members ce env sf tys tvs
    (abi_decode_members (MAP (vyper_to_abi_type env) tys) bs bs) vs /\
  valid_enc_tuple (MAP (vyper_to_abi_type env) tys) bs bs /\
  SUM (MAP abi_member_head_size (MAP (vyper_to_abi_type env) tys)) <= LENGTH bs
Proof
  strip_tac >> drule abi_valid_tuple_source_values >> strip_tac >>
  `LIST_REL (abi_decoder_coherent ce env sf) tys tvs` by fs[abi_decoder_coherent_tuple_iff] >>
  drule_all abi_valid_members_metadata >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_MEMBERS_METADATA_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid member metadata not kernel closed: " ^ n)
  end) (DB.thms "abiValidMembersMetadata");
