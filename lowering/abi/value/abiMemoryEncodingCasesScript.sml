(* TOP-LEVEL: invert recursive ABI memory observations at the exact compiler
   dispatch branches. Helpers identify array live-source and head extents. *)
Theory abiMemoryEncodingCases
Ancestors
  abiMemoryEncoding abiFieldLayoutDefs valueEncodingProofs list rich_list arithmetic words

Theorem abi_memory_word_cases:
  !src span mem payload.
    abi_memory_encoding AbiPrimWord src span mem payload <=>
    32 <= span /\ payload = word_to_bytes (mem_word_at src mem : bytes32) T
Proof
  simp[Once abi_memory_encoding_cases] >> metis_tac[]
QED

Theorem abi_memory_copy_cases:
  !n src span mem payload.
    abi_memory_encoding (AbiCopy n) src span mem payload <=>
    n <= span /\ payload = mem_bytes_at src n mem
Proof
  simp[Once abi_memory_encoding_cases] >> metis_tac[]
QED

Theorem abi_memory_bytes_cases:
  !cap src span mem payload.
    abi_memory_encoding (AbiBytestring cap) src span mem payload <=>
    ?bs. 32 + LENGTH bs <= span /\ LENGTH bs < dimword (:256) /\
      mem_word_at src mem = n2w (LENGTH bs) /\
      mem_bytes_at (src + 32) (LENGTH bs) mem = bs /\
      payload = enc (Bytes NONE) (contractABI$BytesV bs)
Proof
  simp[Once abi_memory_encoding_cases] >> metis_tac[]
QED

Theorem abi_memory_complex_cases:
  !entries src span mem payload.
    abi_memory_encoding (AbiComplex entries) src span mem payload <=>
    ?fields. abi_memory_fields entries src span mem fields /\
      payload = abi_field_bytes (abi_field_head_size fields) fields
Proof
  simp[Once abi_memory_encoding_cases] >> metis_tac[]
QED

Theorem abi_memory_empty_cases:
  !src span mem payload.
    abi_memory_encoding (AbiComplex []) src span mem payload <=> payload = []
Proof
  simp[abi_memory_complex_cases, Once abi_memory_fields_cases,
    abi_field_bytes_def, abi_field_heads_def, abi_field_tails_def]
QED

Theorem abi_memory_array_cases:
  !info abi_sz mem_sz is_dyn src span mem payload.
    abi_memory_encoding (AbiDynArray info abi_sz mem_sz is_dyn) src span mem payload <=>
    ?fields. 32 <= span /\ LENGTH fields < dimword (:256) /\
      mem_word_at src mem = n2w (LENGTH fields) /\
      (~is_dyn ==> abi_sz = abi_static_encoder_size info) /\
      abi_memory_fields (REPLICATE (LENGTH fields) (info,abi_sz,mem_sz,is_dyn))
        (src + 32) (span - 32) mem fields /\
      payload = word_to_bytes (n2w (LENGTH fields) : bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields
Proof
  simp[Once abi_memory_encoding_cases] >> metis_tac[]
QED

Theorem abi_memory_array_source_extent:
  !info abi_sz mem_sz is_dyn src span mem payload.
    abi_memory_encoding (AbiDynArray info abi_sz mem_sz is_dyn) src span mem payload ==>
    ?fields. 32 + LENGTH fields * mem_sz <= span /\
      abi_field_head_size fields = LENGTH fields * abi_sz /\
      mem_word_at src mem = n2w (LENGTH fields) /\
      abi_memory_fields (REPLICATE (LENGTH fields) (info,abi_sz,mem_sz,is_dyn))
        (src + 32) (span - 32) mem fields /\
      payload = word_to_bytes (n2w (LENGTH fields) : bytes32) T ++
        abi_field_bytes (abi_field_head_size fields) fields
Proof
  simp_tac bool_ss [abi_memory_array_cases] >> rpt strip_tac >>
  drule abi_memory_fields_source_size >>
  simp[] >> DISCH_TAC >>
  drule abi_memory_fields_head_size >>
  simp[] >> DISCH_TAC >>
  qexists_tac `fields` >> simp[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI memory cases: " ^ name)
  end) (DB.thms "abiMemoryEncodingCases")
