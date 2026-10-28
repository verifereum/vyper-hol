(* TOP-LEVEL: arbitrary recursive encoder results advance the aggregate's
   source suffix and completed head/tail layout. All concrete output and
   scratch writes participate in the frame conditions; no field family is
   restricted to scalar, bytestring or bytestring-array payloads. *)
Theory abiMemoryFieldsAdvance
Ancestors
  abiMemoryFieldsState abiMemoryRunFrame abiMemoryLeafRun abiMemoryFieldEntry
  abiFieldCompose abiFieldMemory abiFieldLayoutDefs abiStaticFieldMemory abiFieldBytesPath
  abiMemoryFrame memoryReadProps compileEnv venomState list words arithmetic

Definition abi_encoding_writes_def:
  abi_encoding_writes (encoded_addr:bytes32) payload scratch =
    (w2n encoded_addr,LENGTH payload)::scratch
End

Theorem abi_memory_fields_next_source:
  !ctx func cs mid ret encoded_addr payload scratch ss out done info abi_sz mem_sz is_dyn rest fields
      tail_start dst_addr dyn_addr root_addr source_capacity source_offset.
    abi_memory_fields_data done ((info,abi_sz,mem_sz,is_dyn)::rest) ((is_dyn,payload)::fields)
      tail_start dst_addr dyn_addr root_addr source_capacity source_offset ss /\
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
  rpt gen_tac >> strip_tac >> drule abi_memory_fields_data_source >> strip_tac >>
  `w2n root_addr + source_capacity < dimword (:256)` by fs[abi_memory_fields_data_def] >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `encoded_addr`, `payload`, `scratch`,
    `ss`, `out`, `rest`, `w2n root_addr + source_offset + mem_sz`,
    `source_capacity - (source_offset + mem_sz)`, `fields`] mp_tac abi_encoding_result_fields >>
  impl_tac >- fs[abi_encoding_writes_def] >> simp[]
QED

Theorem abi_memory_fields_static_advance:
  !ctx func cs mid ret payload scratch ss out done info abi_sz mem_sz rest fields
      tail_start dst_addr dyn_addr root_addr source_capacity source_offset.
    abi_memory_fields_data done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
      tail_start dst_addr dyn_addr root_addr source_capacity source_offset ss /\
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
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n dyn_addr) 32 write_base write_count)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) ==>
    abi_memory_fields_data (done ++ [(F,payload)]) rest fields tail_start dst_addr dyn_addr root_addr
      source_capacity (source_offset + mem_sz) out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_fields_next_source >> strip_tac >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss` by
    (qspecl_then [`(w2n (dst_addr + n2w (abi_field_head_size done)),LENGTH payload)::scratch`,
       `ss`, `out`, `w2n dyn_addr`] mp_tac abi_memory_frame_mload >>
     impl_tac >- fs[abi_encoding_writes_def] >> simp[]) >>
  `read_memory (w2n dst_addr + abi_field_head_size done) (LENGTH payload) out = payload` by
    (irule abi_static_field_read >> fs[]) >>
  `abi_fields_layout (done ++ [(F,payload)]) (w2n dst_addr) 0 tail_start out` by
    (qspecl_then [`done`, `payload`, `w2n dst_addr`, `0`, `tail_start`,
       `(w2n (dst_addr + n2w (abi_field_head_size done)),LENGTH payload)::scratch`, `ss`, `out`]
       mp_tac abi_fields_layout_static_extend >>
     impl_tac >- (gvs[abi_memory_fields_data_def, abi_encoding_writes_def] >>
       simp[abi_window_separated_def, read_memory_def]) >> simp[]) >>
  fs[abi_memory_fields_data_def, abi_field_tail_size_append, abi_field_tail_def]
QED

Theorem abi_memory_fields_dynamic_advance:
  !ctx func cs mid ret payload scratch ss out done info abi_sz mem_sz rest fields
      tail_start dst_addr dyn_addr root_addr source_capacity source_offset.
    abi_memory_fields_data done ((info,abi_sz,mem_sz,T)::rest) ((T,payload)::fields)
      tail_start dst_addr dyn_addr root_addr source_capacity source_offset ss /\
    abi_encoding_result ctx func cs mid ret (dst_addr + mload (w2n dyn_addr) ss) payload scratch ss out /\
    mload (w2n (dst_addr + n2w (abi_field_head_size done))) out = mload (w2n dyn_addr) ss /\
    mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss + n2w (LENGTH payload) /\
    w2n dst_addr + abi_field_head_size done < dimword (:256) /\
    w2n dst_addr + (tail_start + abi_field_tail_size done) < dimword (:256) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n root_addr + source_offset + mem_sz)
        (source_capacity - (source_offset + mem_sz)) write_base write_count)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload scratch) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n dst_addr) (abi_field_head_size done) write_base write_count)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload scratch) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n dst_addr + tail_start) (abi_field_tail_size done) write_base write_count)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload scratch) ==>
    abi_memory_fields_data (done ++ [(T,payload)]) rest fields tail_start dst_addr dyn_addr root_addr
      source_capacity (source_offset + mem_sz) out
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_fields_next_source >> strip_tac >>
  qpat_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  `mload (w2n dyn_addr) ss = n2w (tail_start + abi_field_tail_size done)` by
    fs[abi_memory_fields_data_def] >>
  `w2n (dst_addr + n2w (abi_field_head_size done)) = w2n dst_addr + abi_field_head_size done` by
    (irule abi_field_word_address >> simp[]) >>
  `w2n (dst_addr + mload (w2n dyn_addr) ss) = w2n dst_addr + (tail_start + abi_field_tail_size done)` by
    (asm_simp_tac bool_ss [] >> irule abi_field_word_address >> simp[]) >>
  `mload (w2n dst_addr + abi_field_head_size done) out = n2w (tail_start + abi_field_tail_size done)` by
    (qpat_x_assum `mload (w2n (dst_addr + n2w (abi_field_head_size done))) out = _` mp_tac >> simp[]) >>
  `read_memory (w2n dst_addr + tail_start + abi_field_tail_size done) (LENGTH payload) out = payload` by
    (`w2n dst_addr + tail_start + abi_field_tail_size done =
      w2n (dst_addr + mload (w2n dyn_addr) ss)` by decide_tac >>
     pop_assum SUBST1_TAC >> first_assum MATCH_ACCEPT_TAC) >>
  `abi_fields_layout (done ++ [(T,payload)]) (w2n dst_addr) 0 tail_start out` by
    (qspecl_then [`done`, `payload`, `w2n dst_addr`, `0`, `tail_start`,
       `(w2n (dst_addr + mload (w2n dyn_addr) ss),LENGTH payload)::scratch`, `ss`, `out`]
       mp_tac abi_fields_layout_dynamic_extend >>
     impl_tac >- fs[abi_memory_fields_data_def, abi_encoding_writes_def] >> simp[]) >>
  fs[abi_memory_fields_data_def, abi_field_tail_size_append, abi_field_tail_def, word_add_n2w]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed arbitrary recursive ABI traversal advance: " ^ name)
  end) (DB.thms "abiMemoryFieldsAdvance")
