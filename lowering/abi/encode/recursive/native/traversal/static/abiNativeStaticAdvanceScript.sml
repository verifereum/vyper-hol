(* TOP-LEVEL: an actual child result advances the aligned static traversal
   state and its remaining semantic child assertions together. *)
Theory abiNativeStaticAdvance
Ancestors
  abiNativeStaticState abiNativeFields abiMemoryFieldsLayoutAdvance abiMemoryFieldsLayout
  abiMemoryFieldsState abiMemoryLeafRun abiMemoryFieldsAdvance abiFieldLayoutDefs abiMemoryFrame
  compileEnv venomState list pair words arithmetic

Theorem abi_native_static_advance:
  !ctx func full done fields dst src dst_addr root_addr source_capacity reference info abi_sz mem_sz rest
      source_offset cs mid ret payload scratch ss out.
    EVERY (\(is_dyn,bytes). ~is_dyn) full /\ full = done ++ ((F,payload)::fields) /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss /\
    abi_memory_fields_layout done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
      (abi_field_head_size full) dst_addr root_addr source_capacity source_offset ss /\
    abi_native_fields rest (w2n root_addr + source_offset + mem_sz) reference fields /\
    cs.cs_next_var <= mid.cs_next_var /\
    abi_encoding_result ctx func cs mid ret (dst_addr + n2w (abi_field_head_size done))
      payload scratch ss out /\
    (LENGTH payload = 0 \/ w2n dst_addr + abi_field_head_size done < dimword (:256)) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n root_addr + source_offset + mem_sz)
        (source_capacity - (source_offset + mem_sz)) write_base write_count)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) /\
    EVERY (\(write_base,write_count).
      abi_window_separated (w2n dst_addr) (abi_field_head_size done) write_base write_count)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) ==>
    abi_native_static_state full dst src dst_addr root_addr source_capacity reference rest
      (source_offset + mem_sz) (abi_field_head_size done + abi_sz) mid out
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `abi_field_tail_size done = 0` by
    (qspecl_then [`done`, `abi_field_head_size full`] mp_tac abi_static_field_payloads >>
     impl_tac >- fs[EVERY_APPEND] >> simp[]) >>
  `EVERY (\(write_base,write_count).
      abi_window_separated (w2n dst_addr + abi_field_head_size full) (abi_field_tail_size done)
        write_base write_count)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch)` by
    simp[abi_window_separated_def, EVERY_MEM, FORALL_PROD] >>
  `abi_sz = LENGTH payload` by (drule abi_memory_fields_layout_source >> simp[]) >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `payload`, `scratch`, `ss`, `out`,
    `done`, `info`, `abi_sz`, `mem_sz`, `rest`, `fields`, `abi_field_head_size full`,
    `dst_addr`, `root_addr`, `source_capacity`, `source_offset`]
    mp_tac abi_memory_fields_layout_static_advance >>
  impl_tac >- asm_simp_tac bool_ss [] >> DISCH_TAC >>
  qspecl_then [`ctx`, `func`, `cs`, `mid`, `ret`, `dst_addr + n2w (abi_field_head_size done)`,
    `payload`, `scratch`, `ss`, `out`, `dst`, `src`, `Lit 0w`, `dst_addr`, `root_addr`, `0w`]
    mp_tac abi_memory_fields_operands_frame >> impl_tac >- simp[] >> DISCH_TAC >>
  `w2n root_addr + (source_offset + mem_sz) = w2n root_addr + source_offset + mem_sz` by decide_tac >>
  qspecl_then [`full`, `done ++ [(F,payload)]`, `fields`, `dst`, `src`, `dst_addr`, `root_addr`,
    `source_capacity`, `reference`, `rest`, `source_offset + mem_sz`,
    `abi_field_head_size done + abi_sz`, `mid`, `out`] mp_tac abi_native_static_intro >>
  impl_tac >- asm_simp_tac (srw_ss()) [APPEND_ASSOC, abi_field_head_size_append, abi_field_head_size_def] >>
  simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed aligned native static traversal advance: " ^ name)
  end) (DB.thms "abiNativeStaticAdvance")
