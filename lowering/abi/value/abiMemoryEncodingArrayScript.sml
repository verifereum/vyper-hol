(* TOP-LEVEL: assemble recursive array source encodings from their actual
   indexed subvalues. These are initial-memory facts, independent of any
   future execution or child-call contract. *)
Theory abiMemoryEncodingArray
Ancestors
  abiMemoryEncoding abiMemoryEncodingElements abiFieldLayoutDefs
  list rich_list arithmetic words

Theorem abi_memory_elements_tail:
  !info src stride mem payload payloads.
    (!i. i < LENGTH (payload::payloads) ==>
      abi_memory_encoding info (src + i * stride) stride mem (EL i (payload::payloads))) ==>
    !i. i < LENGTH payloads ==>
      abi_memory_encoding info (src + stride + i * stride) stride mem (EL i payloads)
Proof
  rpt gen_tac >> DISCH_TAC >> rpt gen_tac >> DISCH_TAC >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  simp_tac bool_ss [LENGTH, LESS_MONO_EQ, EL, TL, MULT_CLAUSES, ADD_ASSOC] >> simp[]
QED

Theorem abi_memory_fields_from_elements:
  !payloads info abi_sz mem_sz is_dyn src span mem.
    LENGTH payloads * mem_sz <= span /\
    EVERY (\payload. abi_sz = (if is_dyn then 32 else LENGTH payload)) payloads /\
    (!i. i < LENGTH payloads ==>
      abi_memory_encoding info (src + i * mem_sz) mem_sz mem (EL i payloads)) ==>
    abi_memory_fields (REPLICATE (LENGTH payloads) (info,abi_sz,mem_sz,is_dyn))
      src span mem (MAP (\payload. (is_dyn,payload)) payloads)
Proof
  Induct_on `payloads` >- simp[abi_memory_encoding_fields_nil] >>
  rpt gen_tac >> strip_tac >>
  rename1 `LENGTH (payload::payloads) * mem_sz <= span` >>
  `mem_sz <= span /\ LENGTH payloads * mem_sz <= span - mem_sz` by
    (fs[MULT_CLAUSES] >> decide_tac) >>
  `abi_memory_encoding info src mem_sz mem payload` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!i. i < LENGTH payloads ==>
    abi_memory_encoding info (src + mem_sz + i * mem_sz) mem_sz mem (EL i payloads)` by
    (qspecl_then [`info`, `src`, `mem_sz`, `mem`, `payload`, `payloads`]
       mp_tac abi_memory_elements_tail >> simp[]) >>
  simp_tac list_ss [REPLICATE] >>
  irule abi_memory_encoding_fields_cons >> fs[EVERY_DEF] >>
  first_x_assum irule >> fs[]
QED

Theorem abi_memory_array_from_elements:
  !payloads info abi_sz mem_sz is_dyn src span mem.
    32 + LENGTH payloads * mem_sz <= span /\ LENGTH payloads < dimword (:256) /\
    mem_word_at src mem = n2w (LENGTH payloads) /\
    (~is_dyn ==> abi_sz = abi_static_encoder_size info) /\
    EVERY (\payload. abi_sz = (if is_dyn then 32 else LENGTH payload)) payloads /\
    (!i. i < LENGTH payloads ==>
      abi_memory_encoding info (src + 32 + i * mem_sz) mem_sz mem (EL i payloads)) ==>
    abi_memory_encoding (AbiDynArray info abi_sz mem_sz is_dyn) src span mem
      (word_to_bytes (n2w (LENGTH payloads) : bytes32) T ++
       abi_field_bytes (abi_field_head_size (MAP (\payload. (is_dyn,payload)) payloads))
         (MAP (\payload. (is_dyn,payload)) payloads))
Proof
  rpt gen_tac >> strip_tac >>
  `32 <= span` by decide_tac >>
  qspecl_then [`info`, `abi_sz`, `mem_sz`, `is_dyn`, `src`, `span`, `mem`,
    `MAP (\payload. (is_dyn,payload)) payloads`]
    (irule o SIMP_RULE list_ss []) abi_memory_encoding_array >> simp[] >>
  irule abi_memory_fields_from_elements >> simp[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI array source construction: " ^ name)
  end) (DB.thms "abiMemoryEncodingArray")
