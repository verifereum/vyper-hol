(* TOP-LEVEL: exact source ABI bytes for arrays with arbitrary recursive
   element types. Helpers instantiate the tuple head/tail correspondence
   and transport it through the encoder's repeated element descriptors. *)
Theory abiMemoryTypedArraySource
Ancestors
  abiMemoryEncoding abiMemoryEncodingArray abiFieldSource abiFieldLayoutDefs
  contractABI list rich_list option pair combin words arithmetic

Theorem abi_array_replicated_fields:
  !vs ty.
    MAP2 (\ty v. (is_dynamic ty, enc ty v)) (REPLICATE (LENGTH vs) ty) vs =
      MAP (\v. (is_dynamic ty, enc ty v)) vs
Proof
  Induct >> simp[]
QED

Theorem abi_array_replicated_static_sizes:
  !vs ty.
    EVERY (\v. ~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) vs ==>
    LIST_REL (\ty v. ~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty)
      (REPLICATE (LENGTH vs) ty) vs
Proof
  Induct >> simp[]
QED

Theorem enc_array_field_bytes:
  !ty vs bound.
    EVERY (\v. ~is_dynamic ty ==> LENGTH (enc ty v) = static_length ty) vs ==>
    enc (Array bound ty) (ListV vs) =
      (case bound of NONE => word_to_bytes (n2w (LENGTH vs):bytes32) T | SOME n => []) ++
      abi_field_bytes (abi_field_head_size (MAP (\v. (is_dynamic ty, enc ty v)) vs))
        (MAP (\v. (is_dynamic ty, enc ty v)) vs)
Proof
  rpt gen_tac >> DISCH_TAC >> drule abi_array_replicated_static_sizes >> DISCH_TAC >>
  drule_then (qspec_then `0` mp_tac) static_field_head_sizes >>
  simp_tac list_ss [abi_array_replicated_fields] >> DISCH_TAC >>
  Cases_on `bound` >> CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [enc_def])) >>
  asm_simp_tac bool_ss [LET_THM] >>
  simp_tac list_ss [enc_tuple_field_parts, abi_array_replicated_fields,
    abi_field_bytes_def, enc_number_def, LENGTH_REPLICATE, REV_REVERSE_LEM, APPEND_ASSOC]
QED

Theorem abi_memory_typed_array_elements:
  !ty avs info abi_sz mem_sz is_dyn source span mem.
    LENGTH avs * mem_sz <= span /\ is_dyn = is_dynamic ty /\
    EVERY (\av. abi_sz = (if is_dyn then 32 else LENGTH (enc ty av))) avs /\
    (!i. i < LENGTH avs ==>
      abi_memory_encoding info (source + i * mem_sz) mem_sz mem (enc ty (EL i avs))) ==>
    abi_memory_fields (REPLICATE (LENGTH avs) (info,abi_sz,mem_sz,is_dyn)) source span mem
      (MAP (\av. (is_dynamic ty, enc ty av)) avs)
Proof
  rpt gen_tac >> strip_tac >>
  `MAP (\payload. (is_dyn,payload)) (MAP (enc ty) avs) =
     MAP (\av. (is_dynamic ty, enc ty av)) avs` by simp[MAP_MAP_o, o_DEF] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
  qspecl_then [`MAP (enc ty) avs`, `info`, `abi_sz`, `mem_sz`, `is_dyn`, `source`, `span`, `mem`]
    mp_tac abi_memory_fields_from_elements >> simp[EVERY_MAP, EL_MAP]
QED

Theorem abi_memory_typed_array_source:
  !ty avs info abi_sz mem_sz is_dyn source span mem.
    32 + LENGTH avs * mem_sz <= span /\ LENGTH avs < dimword (:256) /\
    mem_word_at source mem = n2w (LENGTH avs) /\ is_dyn = is_dynamic ty /\
    (~is_dyn ==> abi_sz = abi_static_encoder_size info) /\
    EVERY (\av. abi_sz = (if is_dyn then 32 else LENGTH (enc ty av))) avs /\
    EVERY (\av. ~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty) avs /\
    (!i. i < LENGTH avs ==>
      abi_memory_encoding info (source + 32 + i * mem_sz) mem_sz mem (enc ty (EL i avs))) ==>
    abi_memory_encoding (AbiDynArray info abi_sz mem_sz is_dyn) source span mem
      (enc (Array NONE ty) (ListV avs))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `is_dyn = is_dynamic ty` SUBST_ALL_TAC >>
  drule_then (qspec_then `NONE` mp_tac) enc_array_field_bytes >>
  simp_tac list_ss [] >> disch_then SUBST1_TAC >>
  qspecl_then [`info`, `abi_sz`, `mem_sz`, `is_dynamic ty`, `source`, `span`, `mem`,
    `MAP (\av. (is_dynamic ty, enc ty av)) avs`]
    (irule o SIMP_RULE list_ss []) abi_memory_encoding_array >> simp[] >>
  irule abi_memory_typed_array_elements >> fs[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI array source correspondence: " ^ name)
  end) (DB.thms "abiMemoryTypedArraySource")
