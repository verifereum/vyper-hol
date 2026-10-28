(* TOP-LEVEL: actual static and dynamic child results advance the mixed
   traversal state, retaining semantic assertions for exactly its suffix. *)
Theory abiNativeDynamicAdvance
Ancestors
  abiNativeDynamicState abiNativeFields abiMemoryFieldsState abiMemoryFieldsAdvance abiMemoryLeafRun
  abiFieldLayoutDefs abiMemoryFrame compileEnv venomState list pair words arithmetic

Theorem abi_native_dynamic_static_advance:
  !ctx func full done fields dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      info abi_sz mem_sz rest source_offset cs mid ret payload scratch ss out.
    full = done ++ ((F,payload)::fields) /\
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    abi_memory_fields_data done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
      (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss /\
    abi_native_fields rest (w2n root_addr + source_offset + mem_sz) reference fields /\
    cs.cs_next_var <= mid.cs_next_var /\
    abi_encoding_result ctx func cs mid ret (dst_addr + n2w (abi_field_head_size done)) payload scratch ss out /\
    (LENGTH payload = 0 \/ w2n dst_addr + abi_field_head_size done < dimword (:256)) /\
    EVERY (\(b,n). abi_window_separated (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) b n)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) (abi_field_head_size done) b n)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + abi_field_head_size full) (abi_field_tail_size done) b n)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) /\
    EVERY (\(b,n). abi_window_separated (w2n dyn_addr) 32 b n)
      (abi_encoding_writes (dst_addr + n2w (abi_field_head_size done)) payload scratch) ==>
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference rest
      (source_offset + mem_sz) (abi_field_head_size done + abi_sz) mid out
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `abi_sz = LENGTH payload` by (drule abi_memory_fields_data_source >> simp[]) >>
  drule_all abi_memory_fields_static_advance >> DISCH_TAC >>
  drule_all abi_memory_fields_operands_frame >> DISCH_TAC >>
  `w2n root_addr + (source_offset + mem_sz) = w2n root_addr + source_offset + mem_sz` by decide_tac >>
  qspecl_then [`full`, `done ++ [(F,payload)]`, `fields`, `dst`, `src`, `dyn_ptr`, `dst_addr`, `dyn_addr`,
    `root_addr`, `source_capacity`, `reference`, `rest`, `source_offset + mem_sz`,
    `abi_field_head_size done + abi_sz`, `mid`, `out`] mp_tac abi_native_dynamic_intro >>
  impl_tac >- asm_simp_tac (srw_ss()) [APPEND_ASSOC, abi_field_head_size_append, abi_field_head_size_def] >> simp[]
QED

Theorem abi_native_dynamic_dynamic_advance:
  !ctx func full done fields dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      info abi_sz mem_sz rest source_offset cs mid ret payload scratch ss out.
    full = done ++ ((T,payload)::fields) /\
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    abi_memory_fields_data done ((info,abi_sz,mem_sz,T)::rest) ((T,payload)::fields)
      (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss /\
    abi_native_fields rest (w2n root_addr + source_offset + mem_sz) reference fields /\
    cs.cs_next_var <= mid.cs_next_var /\
    abi_encoding_result ctx func cs mid ret (dst_addr + mload (w2n dyn_addr) ss) payload scratch ss out /\
    mload (w2n (dst_addr + n2w (abi_field_head_size done))) out = mload (w2n dyn_addr) ss /\
    mload (w2n dyn_addr) out = mload (w2n dyn_addr) ss + n2w (LENGTH payload) /\
    w2n dst_addr + abi_field_head_size done < dimword (:256) /\
    w2n dst_addr + (abi_field_head_size full + abi_field_tail_size done) < dimword (:256) /\
    EVERY (\(b,n). abi_window_separated (w2n root_addr + source_offset + mem_sz)
      (source_capacity - (source_offset + mem_sz)) b n)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload scratch) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) (abi_field_head_size done) b n)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload scratch) /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + abi_field_head_size full) (abi_field_tail_size done) b n)
      (abi_encoding_writes (dst_addr + mload (w2n dyn_addr) ss) payload scratch) ==>
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference rest
      (source_offset + mem_sz) (abi_field_head_size done + abi_sz) mid out
Proof
  rpt gen_tac >> disch_then (MAP_EVERY ASSUME_TAC o CONJUNCTS) >>
  `abi_sz = 32` by (drule abi_memory_fields_data_source >> simp[]) >>
  drule_all abi_memory_fields_dynamic_advance >> DISCH_TAC >>
  drule_all abi_memory_fields_operands_frame >> DISCH_TAC >>
  `w2n root_addr + (source_offset + mem_sz) = w2n root_addr + source_offset + mem_sz` by decide_tac >>
  qspecl_then [`full`, `done ++ [(T,payload)]`, `fields`, `dst`, `src`, `dyn_ptr`, `dst_addr`, `dyn_addr`,
    `root_addr`, `source_capacity`, `reference`, `rest`, `source_offset + mem_sz`,
    `abi_field_head_size done + abi_sz`, `mid`, `out`] mp_tac abi_native_dynamic_intro >>
  impl_tac >- asm_simp_tac (srw_ss()) [APPEND_ASSOC, abi_field_head_size_append, abi_field_head_size_def] >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed aligned native mixed traversal advance: " ^ name)
  end) (DB.thms "abiNativeDynamicAdvance")
