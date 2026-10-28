(* TOP-LEVEL: the complete static payload bounds every field's physical
   source and destination subwindows, including zero-length fields. *)
Theory abiNativeStaticBounds
Ancestors
  abiNativeEncodingDefs abiMemoryFieldsLayout abiMemoryFieldEntry abiFieldLayoutDefs abiFieldBytesPath
  compileEnv venomState list words arithmetic

Theorem abi_native_static_field_bounds:
  !func root_cs root_after source_id target_id initial full done payload fields dst_addr root_addr
      source_capacity source_offset info abi_sz mem_sz rest ss.
    full = done ++ ((F,payload)::fields) /\ EVERY (\(is_dyn,bytes). ~is_dyn) full /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_memory_fields_layout done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
      (abi_field_head_size full) dst_addr root_addr source_capacity source_offset ss ==>
    abi_sz = LENGTH payload /\ source_offset + mem_sz <= source_capacity /\
    w2n root_addr + source_offset < dimword (:256) /\
    w2n dst_addr + abi_field_head_size done < dimword (:256) /\
    w2n (root_addr + n2w source_offset) = w2n root_addr + source_offset /\
    w2n (dst_addr + n2w (abi_field_head_size done)) = w2n dst_addr + abi_field_head_size done /\
    w2n root_addr <= w2n (root_addr + n2w source_offset) /\
    w2n (root_addr + n2w source_offset) + mem_sz <= w2n root_addr + source_capacity /\
    w2n dst_addr <= w2n (dst_addr + n2w (abi_field_head_size done)) /\
    w2n (dst_addr + n2w (abi_field_head_size done)) + LENGTH payload <=
      w2n dst_addr + LENGTH (abi_field_bytes (abi_field_head_size full) full)
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_memory_bounds >> strip_tac >>
  drule abi_memory_fields_layout_source >> strip_tac >>
  `abi_field_head_size full = abi_field_head_size done + (LENGTH payload + abi_field_head_size fields)` by
    (qpat_x_assum `full = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[abi_field_head_size_append, abi_field_head_size_def]) >>
  `abi_field_tail_size full = 0` by
    (qspecl_then [`full`, `abi_field_head_size full`] mp_tac abi_static_field_payloads >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  `LENGTH (abi_field_bytes (abi_field_head_size full) full) = abi_field_head_size full` by simp[] >>
  `w2n dst_addr + abi_field_head_size done < dimword (:256)` by decide_tac >>
  `w2n (root_addr + n2w source_offset) = w2n root_addr + source_offset` by
    (irule abi_field_word_address >> simp[]) >>
  `w2n (dst_addr + n2w (abi_field_head_size done)) = w2n dst_addr + abi_field_head_size done` by
    (irule abi_field_word_address >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete static field window bounds: " ^ name)
  end) (DB.thms "abiNativeStaticBounds")
