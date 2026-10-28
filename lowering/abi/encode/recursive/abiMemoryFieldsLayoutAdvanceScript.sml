(* TOP-LEVEL: an arbitrary recursive static child advances source and output
   layout without a parent counter or a counter-separation premise.
   Helpers preserve unread source and the previously completed heads/tails. *)
Theory abiMemoryFieldsLayoutAdvance
Ancestors
  abiMemoryFieldsLayout abiMemoryRunFrame abiMemoryLeafRun abiMemoryFieldsAdvance
  abiFieldCompose abiFieldMemory abiFieldLayoutDefs abiStaticFieldMemory abiFieldBytesPath
  abiMemoryFrame compileEnv venomState list words arithmetic

Theorem abi_memory_fields_layout_next_source:
  !ctx func cs mid ret encoded_addr payload scratch ss out done info abi_sz mem_sz is_dyn rest fields
      tail_start dst_addr root_addr source_capacity source_offset.
    abi_memory_fields_layout done ((info,abi_sz,mem_sz,is_dyn)::rest) ((is_dyn,payload)::fields)
      tail_start dst_addr root_addr source_capacity source_offset ss /\
    abi_encoding_result ctx func cs mid ret encoded_addr payload scratch ss out /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n root_addr + source_offset + mem_sz)
        (source_capacity - (source_offset + mem_sz)) write_base write_count)
      (abi_encoding_writes encoded_addr payload scratch) ==>
    source_offset + mem_sz <= source_capacity /\
    w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields rest (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) out.vs_memory fields
Proof
  rpt gen_tac >> strip_tac >> drule abi_memory_fields_layout_source >> strip_tac >>
  `w2n root_addr + source_capacity < dimword (:256)` by fs[abi_memory_fields_layout_def] >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `encoded_addr`, `payload`, `scratch`,
    `ss`, `out`, `rest`, `w2n root_addr + source_offset + mem_sz`,
    `source_capacity - (source_offset + mem_sz)`, `fields`] mp_tac abi_encoding_result_fields >>
  impl_tac >- fs[abi_encoding_writes_def] >> simp[]
QED

Theorem abi_memory_fields_layout_static_advance:
  !ctx func cs mid ret payload scratch ss out done info abi_sz mem_sz rest fields
      tail_start dst_addr root_addr source_capacity source_offset.
    abi_memory_fields_layout done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
      tail_start dst_addr root_addr source_capacity source_offset ss /\
    abi_encoding_result ctx func cs mid ret (dst_addr + n2w (abi_field_head_size done))
      payload scratch ss out /\
    (LENGTH payload = 0 \/ w2n dst_addr + abi_field_head_size done < dimword (:256)) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n root_addr + source_offset + mem_sz)
        (source_capacity - (source_offset + mem_sz)) write_base write_count)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n dst_addr) (abi_field_head_size done) write_base write_count)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n dst_addr + tail_start) (abi_field_tail_size done) write_base write_count)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) ==>
    abi_memory_fields_layout (done ++ [(F,payload)]) rest fields tail_start dst_addr root_addr
      source_capacity (source_offset + mem_sz) out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_fields_layout_next_source >> strip_tac >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `read_memory (w2n dst_addr + abi_field_head_size done) (LENGTH payload) out = payload` by
    (irule abi_static_field_read >> fs[]) >>
  `abi_fields_layout (done ++ [(F,payload)]) (w2n dst_addr) 0 tail_start out` by
    (qspecl_then [`done`, `payload`, `w2n dst_addr`, `0`, `tail_start`,
       `(w2n (dst_addr + n2w (abi_field_head_size done)),LENGTH payload)::scratch`, `ss`, `out`]
       mp_tac abi_fields_layout_static_extend >>
     impl_tac >- (gvs[abi_memory_fields_layout_def, abi_encoding_writes_def] >>
       simp[abi_window_separated_def, read_memory_def]) >> simp[]) >>
  fs[abi_memory_fields_layout_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed counter-free recursive ABI child layout advance: " ^ name)
  end) (DB.thms "abiMemoryFieldsLayoutAdvance")
