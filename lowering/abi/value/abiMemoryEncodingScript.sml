(* TOP-LEVEL: source memory and complete ABI bytes for arbitrary recursive
   encoder metadata. Capacities bound reads, including live array elements;
   unused source capacity is unrestricted. No execution contract is assumed.
   Helper: the static array loop's exact dispatcher, including its empty
   fallback for metadata that does not arise from static source types. *)
Theory abiMemoryEncoding
Ancestors
  compileEnv valueEncoding abiFieldLayoutDefs contractABI list words arithmetic

Definition abi_static_encoder_size_def:
  abi_static_encoder_size AbiPrimWord = 32 /\
  abi_static_encoder_size (AbiCopy n) = n /\
  abi_static_encoder_size _ = 0
End

Inductive abi_memory_encoding:
[~word:]
  (!src span mem.
    32 <= span ==>
    abi_memory_encoding AbiPrimWord src span mem
      (word_to_bytes (mem_word_at src mem : bytes32) T))
[~copy:]
  (!n src span mem.
    n <= span ==>
    abi_memory_encoding (AbiCopy n) src span mem (mem_bytes_at src n mem))
[~bytes:]
  (!cap src span mem bs.
    32 + LENGTH bs <= span /\ LENGTH bs < dimword (:256) /\
    mem_word_at src mem = n2w (LENGTH bs) /\
    mem_bytes_at (src + 32) (LENGTH bs) mem = bs ==>
    abi_memory_encoding (AbiBytestring cap) src span mem
      (enc (Bytes NONE) (contractABI$BytesV bs)))
[~complex:]
  (!entries src span mem fields.
    abi_memory_fields entries src span mem fields ==>
    abi_memory_encoding (AbiComplex entries) src span mem
      (abi_field_bytes (abi_field_head_size fields) fields))
[~array:]
  (!info abi_sz mem_sz is_dyn src span mem fields.
    32 <= span /\ LENGTH fields < dimword (:256) /\
    mem_word_at src mem = n2w (LENGTH fields) /\
    (~is_dyn ==> abi_sz = abi_static_encoder_size info) /\
    abi_memory_fields (REPLICATE (LENGTH fields) (info,abi_sz,mem_sz,is_dyn))
      (src + 32) (span - 32) mem fields ==>
    abi_memory_encoding (AbiDynArray info abi_sz mem_sz is_dyn) src span mem
      (word_to_bytes (n2w (LENGTH fields) : bytes32) T ++
       abi_field_bytes (abi_field_head_size fields) fields))
[~fields_nil:]
  (!src span mem. abi_memory_fields [] src span mem [])
[~fields_cons:]
  (!info abi_sz mem_sz is_dyn rest src span mem payload fields.
    mem_sz <= span /\
    abi_memory_encoding info src mem_sz mem payload /\
    abi_sz = (if is_dyn then 32 else LENGTH payload) /\
    abi_memory_fields rest (src + mem_sz) (span - mem_sz) mem fields ==>
    abi_memory_fields ((info,abi_sz,mem_sz,is_dyn)::rest) src span mem
      ((is_dyn,payload)::fields))
End

val abi_memory_fields_cases = save_thm ("abi_memory_fields_cases",
  CONJUNCT2 abi_memory_encoding_cases)

Theorem abi_memory_fields_length:
  !entries src span mem fields.
    abi_memory_fields entries src span mem fields ==>
    LENGTH entries = LENGTH fields
Proof
  Induct_on `entries` >> rpt gen_tac >>
  simp[Once abi_memory_fields_cases] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_memory_fields_head_size:
  !entries src span mem fields.
    abi_memory_fields entries src span mem fields ==>
    abi_field_head_size fields = SUM (MAP (\(_,head_sz,_,_). head_sz) entries)
Proof
  Induct_on `entries` >> rpt gen_tac >>
  simp[Once abi_memory_fields_cases] >> rpt strip_tac >>
  gvs[abi_field_head_size_def] >> first_x_assum drule_all >> simp[]
QED

Theorem abi_memory_fields_source_size:
  !entries src span mem fields.
    abi_memory_fields entries src span mem fields ==>
    SUM (MAP (\(_,_,mem_sz,_). mem_sz) entries) <= span
Proof
  Induct_on `entries` >> rpt gen_tac >>
  simp[Once abi_memory_fields_cases] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI source encoding: " ^ name)
  end) (DB.thms "abiMemoryEncoding")
