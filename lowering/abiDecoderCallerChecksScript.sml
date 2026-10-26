(* Caller-interface probes: these do not assert recursive execution. *)
Theory abiDecoderCallerChecks
Ancestors
  abiDecoderCoherence compileVyper compileEnv valueEncoding vyperABI contractABI
  abiDecodeRanges abiDecoderConstructors

Theorem decoder_caller_word:
  abi_decoder_coherent ce env sf (BaseT (UintT 256)) (BaseTV (UintT 256))
Proof
  simp[abi_decoder_uint256_probe]
QED

Theorem decoder_caller_bytes:
  evaluate_type env (BaseT (BytesT (Dynamic n))) =
    SOME (BaseTV (BytesT (Dynamic n))) ==>
  abi_decoder_coherent ce env sf (BaseT (BytesT (Dynamic n)))
    (BaseTV (BytesT (Dynamic n)))
Proof
  strip_tac >>
  simp[abi_decoder_coherent_bytes_iff, abi_decoder_header_def,
       vfmConstantsTheory.word_size_def,
       vyperValueTheory.evaluate_type_def, type_memory_size_def,
       type_memory_bytes_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       abi_member_head_size_def, is_dynamic_def, static_length_def]
QED

Theorem decoder_caller_singleton:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_type env (TupleT [ty]) = SOME (TupleTV [tv]) ==>
  abi_decoder_coherent ce env sf (TupleT [ty]) (TupleTV [tv])
Proof
  strip_tac >> irule decoder_caller_tuple >> simp[]
QED

(* A genuinely constructed acyclic declaration, not an assumed root header. *)
Theorem decoder_caller_constructed_struct:
  ce.ce_struct_fields =
    make_struct_fields_map [StructDecl "S" [("a",BaseT (UintT 256))]] ==>
  abi_decoder_coherent ce
    (type_env [StructDecl "S" [("a",BaseT (UintT 256))]])
    ce.ce_struct_fields (StructT (NONE,"S"))
    (StructTV [("a",BaseTV (UintT 256))])
Proof
  strip_tac >> irule abi_decoder_one_field_struct_realizable >>
  simp[vyperContextTheory.type_env_def,
       vyperContextTheory.type_env_for_module_def,
       make_struct_fields_map_def, build_struct_fields_map_def,
       build_struct_fields_one_def, field_mem_bytes_def,
       vyperValueTheory.evaluate_type_def, valueEncodingTheory.type_memory_size_def,
       nsid_to_string_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* The existing environment agreement ignores flags entirely. *)
Theorem decoder_caller_consistency_does_not_supply_flags:
  ce.ce_flag_n_members (nsid_to_string nsid) = 0 ==>
  sfields_tenv_consistent FEMPTY (FEMPTY |+ (nsid,FlagArgs 256)) /\
  ~abi_decoder_coherent ce (FEMPTY |+ (nsid,FlagArgs 256)) FEMPTY
    (FlagT nsid) (FlagTV 256)
Proof
  strip_tac >> conj_tac
  >- simp[sfields_tenv_consistent_def, finite_mapTheory.FLOOKUP_UPDATE,
          finite_mapTheory.FLOOKUP_EMPTY] >>
  irule abi_decoder_flag_inconsistent_excluded >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CALLER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI decoder caller probe not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCallerChecks");

