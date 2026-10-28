(* TOP-LEVEL: source suffix and completed ABI heads/tails without a physical
   parent counter. This layout is shared by both aggregate compiler branches.
   Helpers relate the existing counter invariant and extract source/final bytes. *)
Theory abiMemoryFieldsLayout
Ancestors
  abiMemoryFieldsState abiMemoryEncoding abiMemoryFieldEntry abiFieldMemory
  abiFieldLayoutDefs compileEnv venomState list pair words arithmetic

Definition abi_memory_fields_layout_def:
  abi_memory_fields_layout done entries remaining tail_start (dst_addr:bytes32)
      (root_addr:bytes32) source_capacity source_offset ss <=>
    source_offset <= source_capacity /\ w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields entries (w2n root_addr + source_offset) (source_capacity - source_offset)
      ss.vs_memory remaining /\
    abi_fields_layout done (w2n dst_addr) 0 tail_start ss
End

Theorem abi_memory_fields_data_layout:
  !done entries remaining tail_start dst_addr dyn_addr root_addr source_capacity source_offset ss.
    abi_memory_fields_data done entries remaining tail_start dst_addr dyn_addr root_addr
      source_capacity source_offset ss <=>
    abi_memory_fields_layout done entries remaining tail_start dst_addr root_addr
      source_capacity source_offset ss /\
    mload (w2n dyn_addr) ss = n2w (tail_start + abi_field_tail_size done)
Proof
  simp[abi_memory_fields_data_def, abi_memory_fields_layout_def, CONJ_ASSOC]
QED

Theorem abi_memory_fields_layout_initial:
  !full entries tail_start dst_addr root_addr source_capacity ss.
    w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields entries (w2n root_addr) source_capacity ss.vs_memory full ==>
    abi_memory_fields_layout [] entries full tail_start dst_addr root_addr source_capacity 0 ss
Proof
  simp[abi_memory_fields_layout_def]
QED

Theorem abi_memory_fields_layout_memory:
  !done entries remaining tail_start dst_addr root_addr source_capacity source_offset before after.
    after.vs_memory = before.vs_memory ==>
    (abi_memory_fields_layout done entries remaining tail_start dst_addr root_addr
      source_capacity source_offset after =
     abi_memory_fields_layout done entries remaining tail_start dst_addr root_addr
      source_capacity source_offset before)
Proof
  simp[abi_memory_fields_layout_def, abi_fields_layout_def, read_memory_def]
QED

Theorem abi_memory_fields_layout_source:
  !done info abi_sz mem_sz is_dyn rest payload fields tail_start dst_addr root_addr
      source_capacity source_offset ss.
    abi_memory_fields_layout done ((info,abi_sz,mem_sz,is_dyn)::rest) ((is_dyn,payload)::fields)
      tail_start dst_addr root_addr source_capacity source_offset ss ==>
    source_offset + mem_sz <= source_capacity /\
    w2n root_addr + source_offset < dimword (:256) /\
    abi_memory_encoding info (w2n root_addr + source_offset) mem_sz ss.vs_memory payload /\
    abi_memory_fields rest (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) ss.vs_memory fields /\
    abi_sz = (if is_dyn then 32 else LENGTH payload)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_fields_layout_def, abi_memory_fields_cons_cases] >>
  rpt strip_tac >> fs[SUB_SUB] >> decide_tac
QED

Theorem abi_memory_fields_layout_complete:
  !done remaining dst_addr root_addr source_capacity source_offset ss.
    abi_memory_fields_layout done [] remaining (abi_field_head_size done) dst_addr root_addr
      source_capacity source_offset ss ==>
    remaining = [] /\
    read_memory (w2n dst_addr) (LENGTH (abi_field_bytes (abi_field_head_size done) done)) ss =
      abi_field_bytes (abi_field_head_size done) done
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_fields_layout_def] >> strip_tac >>
  `remaining = []` by (drule abi_memory_fields_length >> simp[]) >> simp[] >>
  drule abi_fields_layout_contiguous >> simp[]
QED

Theorem abi_static_field_payloads:
  !fields tail_start.
    EVERY (\(is_dyn,payload). ~is_dyn) fields ==>
    abi_field_tail_size fields = 0 /\
    abi_field_bytes tail_start fields = FLAT (MAP SND fields)
Proof
  Induct_on `fields` >- simp[abi_field_bytes_def, abi_field_heads_def, abi_field_tails_def] >>
  Cases >> rw[] >> fs[abi_field_bytes_def, abi_field_heads_def, abi_field_tails_def,
    abi_field_head_def, abi_field_tail_def, abi_field_tail_size_def, APPEND_ASSOC] >>
  rename1 `abi_field_heads cursor fields = _` >>
  first_x_assum (qspec_then `cursor` mp_tac) >> strip_tac >> gvs[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed recursive ABI layout without a counter: " ^ name)
  end) (DB.thms "abiMemoryFieldsLayout")
