(* TOP-LEVEL: completed heads and tails bound every static or dynamic
   child inside the complete output payload. Cursor offsets do not wrap. *)
Theory abiNativeDynamicBounds
Ancestors
  abiNativeEncodingDefs abiMemoryFieldsState abiMemoryFieldEntry abiFieldLayoutDefs abiFieldBytesPath
  abiMemoryFrame compileEnv venomState list words arithmetic

Theorem abi_native_field_ranges:
  !full done is_dyn payload fields.
    full = done ++ ((is_dyn,payload)::fields) ==>
    abi_field_head_size done + (if is_dyn then 32 else LENGTH payload) <= abi_field_head_size full /\
    abi_field_tail_size done + (if is_dyn then LENGTH payload else 0) <= abi_field_tail_size full
Proof
  rpt gen_tac >> DISCH_TAC >>
  `abi_field_head_size full = abi_field_head_size done +
    ((if is_dyn then 32 else LENGTH payload) + abi_field_head_size fields)` by
    (qpat_assum `full = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[abi_field_head_size_append, abi_field_head_size_def]) >>
  `abi_field_tail_size full = abi_field_tail_size done +
    ((if is_dyn then LENGTH payload else 0) + abi_field_tail_size fields)` by
    (qpat_assum `full = _` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     Cases_on `is_dyn` >> simp[abi_field_tail_size_append, abi_field_tail_def] >> decide_tac) >>
  Cases_on `is_dyn` >> asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem abi_native_dynamic_field_bounds:
  !func root_cs root_after source_id target_id initial full done payload fields dst_addr dyn_addr root_addr
      source_capacity source_offset info abi_sz mem_sz is_dyn rest ss.
    full = done ++ ((is_dyn,payload)::fields) /\
    abi_native_memory_ready func root_cs root_after source_id target_id root_addr source_capacity dst_addr
      (abi_field_bytes (abi_field_head_size full) full) initial /\
    abi_memory_fields_data done ((info,abi_sz,mem_sz,is_dyn)::rest) ((is_dyn,payload)::fields)
      (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss ==>
    abi_sz = (if is_dyn then 32 else LENGTH payload) /\ source_offset + mem_sz <= source_capacity /\
    w2n root_addr + source_offset < dimword (:256) /\
    w2n dst_addr + abi_field_head_size done < dimword (:256) /\
    w2n dst_addr + (abi_field_head_size full + abi_field_tail_size done) < dimword (:256) /\
    mload (w2n dyn_addr) ss = n2w (abi_field_head_size full + abi_field_tail_size done) /\
    w2n (root_addr + n2w source_offset) = w2n root_addr + source_offset /\
    w2n (dst_addr + n2w (abi_field_head_size done)) = w2n dst_addr + abi_field_head_size done /\
    w2n (dst_addr + mload (w2n dyn_addr) ss) =
      w2n dst_addr + (abi_field_head_size full + abi_field_tail_size done) /\
    w2n root_addr <= w2n (root_addr + n2w source_offset) /\
    w2n (root_addr + n2w source_offset) + mem_sz <= w2n root_addr + source_capacity /\
    w2n dst_addr <= w2n (if is_dyn then dst_addr + mload (w2n dyn_addr) ss
      else dst_addr + n2w (abi_field_head_size done)) /\
    w2n (if is_dyn then dst_addr + mload (w2n dyn_addr) ss
      else dst_addr + n2w (abi_field_head_size done)) + LENGTH payload <=
      w2n dst_addr + LENGTH (abi_field_bytes (abi_field_head_size full) full) /\
    abi_field_head_size done + (if is_dyn then 32 else LENGTH payload) <= abi_field_head_size full /\
    abi_field_tail_size done + (if is_dyn then LENGTH payload else 0) <= abi_field_tail_size full
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_memory_bounds >> strip_tac >>
  drule abi_memory_fields_data_source >> strip_tac >>
  drule abi_native_field_ranges >> strip_tac >>
  qpat_x_assum `full = _` kall_tac >>
  `LENGTH (abi_field_bytes (abi_field_head_size full) full) =
    abi_field_head_size full + abi_field_tail_size full` by simp[] >>
  `abi_field_head_size done <= abi_field_head_size full /\
    abi_field_tail_size done <= abi_field_tail_size full` by
    (Cases_on `is_dyn` >> RULE_ASSUM_TAC (SIMP_RULE bool_ss []) >> decide_tac) >>
  `w2n dst_addr + abi_field_head_size done < dimword (:256) /\
    w2n dst_addr + (abi_field_head_size full + abi_field_tail_size done) < dimword (:256)` by decide_tac >>
  `mload (w2n dyn_addr) ss = n2w (abi_field_head_size full + abi_field_tail_size done)` by
    (qpat_assum `abi_memory_fields_data _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_memory_fields_data_def]) >>
     first_assum MATCH_ACCEPT_TAC) >>
  `w2n (root_addr + n2w source_offset) = w2n root_addr + source_offset` by
    (irule abi_field_word_address >> simp[]) >>
  `w2n (dst_addr + n2w (abi_field_head_size done)) = w2n dst_addr + abi_field_head_size done` by
    (irule abi_field_word_address >> simp[]) >>
  `w2n (dst_addr + n2w (abi_field_head_size full + abi_field_tail_size done)) =
    w2n dst_addr + (abi_field_head_size full + abi_field_tail_size done)` by
    (irule abi_field_word_address >> simp[]) >>
  `w2n (dst_addr + mload (w2n dyn_addr) ss) =
    w2n dst_addr + (abi_field_head_size full + abi_field_tail_size done)` by
    asm_simp_tac bool_ss [] >>
  Cases_on `is_dyn` >> RULE_ASSUM_TAC (SIMP_RULE bool_ss []) >> asm_simp_tac bool_ss [] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed mixed native field window bounds: " ^ name)
  end) (DB.thms "abiNativeDynamicBounds")
