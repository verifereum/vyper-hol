(* TOP-LEVEL: complete tuple bounds imply the bounds and separation of
   each head and remaining tail. Field pointers do not wrap. *)
Theory typedFieldsSafety
Ancestors
  logBytesStoreProps valueEncoding words arithmetic

Theorem tuple_copy_parts_safety:
  !atv atvs ftv ftvs src_off dst_off limit.
    src_off + type_memory_size (TupleTV (atv::atvs)) < limit /\
    dst_off + type_memory_size (TupleTV (ftv::ftvs)) < limit /\
    (src_off + type_memory_size (TupleTV (atv::atvs)) <= dst_off \/
      dst_off + type_memory_size (TupleTV (ftv::ftvs)) <= src_off) ==>
    src_off + type_memory_size atv < limit /\
    dst_off + type_memory_size ftv < limit /\
    (src_off + type_memory_size atv <= dst_off \/
      dst_off + type_memory_size ftv <= src_off) /\
    src_off + type_memory_size atv + type_memory_size (TupleTV atvs) < limit /\
    dst_off + type_memory_size ftv + type_memory_size (TupleTV ftvs) < limit /\
    (src_off + type_memory_size atv + type_memory_size (TupleTV atvs) <=
        dst_off + type_memory_size ftv \/
      dst_off + type_memory_size ftv + type_memory_size (TupleTV ftvs) <=
        src_off + type_memory_size atv)
Proof
  rpt gen_tac >> simp_tac bool_ss [type_memory_size_def] >> decide_tac
QED

Theorem tuple_copy_field_pointer:
  !addr field_off tv.
    w2n (addr:bytes32) + field_off + type_memory_size tv < dimword(:256) ==>
    w2n (addr + n2w field_off) = w2n addr + field_off /\
    w2n (addr + n2w field_off) + type_memory_size tv < dimword(:256)
Proof
  rpt gen_tac >> DISCH_TAC >>
  `w2n (addr:bytes32) + field_off < dimword(:256)` by decide_tac >>
  drule log_field_address >> simp[]
QED
