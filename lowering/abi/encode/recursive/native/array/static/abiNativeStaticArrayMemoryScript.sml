(* TOP-LEVEL: one actual static-loop memory effect advances the raw array
   invariant. Its concrete read protections are supplied by owned windows;
   encoded width and source stride remain independent. *)
Theory abiNativeStaticArrayMemory
Ancestors
  abiNativeStaticArrayState abiNativeStaticArraySource abiNativeStaticArrayPrefix abiNativeStaticArrayEffects
  abiNativeStaticArrayPayload abiNativeStaticArrayReadFrame abiStaticLoopBody abiStaticLoopRun
  abiMemoryEncoding abiFieldCompose abiFieldMemory abiFieldLayoutDefs abiMemoryFrame
  memoryReadProps valueEncoding compileEnv venomState list rich_list pair words arithmetic

Theorem abi_native_static_array_memory_step:
  !info stride fields dst_addr root_addr counter_addr source_capacity index labels ss.
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity index ss /\ index < LENGTH fields /\ abi_static_encoder_size info < dimword (:256) /\
    w2n (root_addr + 32w + n2w index * n2w stride) = w2n root_addr + 32 + index * stride /\
    w2n (dst_addr + 32w + n2w index * n2w (abi_static_encoder_size info)) =
      w2n dst_addr + 32 + index * abi_static_encoder_size info /\
    EVERY (\(b,n). abi_window_separated (w2n root_addr) source_capacity b n)
      [(w2n dst_addr + 32 + index * abi_static_encoder_size info,abi_static_encoder_size info);(w2n counter_addr,32)] /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr) 32 b n)
      [(w2n dst_addr + 32 + index * abi_static_encoder_size info,abi_static_encoder_size info);(w2n counter_addr,32)] /\
    EVERY (\(b,n). abi_window_separated (w2n dst_addr + 32) (index * abi_static_encoder_size info) b n)
      [(w2n dst_addr + 32 + index * abi_static_encoder_size info,abi_static_encoder_size info);(w2n counter_addr,32)] /\
    abi_window_separated (w2n dst_addr + 32 + index * abi_static_encoder_size info)
      (abi_static_encoder_size info) (w2n counter_addr) 32 ==>
    abi_native_static_array_data info (abi_static_encoder_size info) stride fields dst_addr root_addr counter_addr
      source_capacity (SUC index)
      (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `abi_native_static_array_data _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_native_static_array_data_def]) >>
  qspecl_then [`info`, `stride`, `w2n root_addr + 32`, `source_capacity - 32`, `ss.vs_memory`, `fields`, `index`]
    mp_tac abi_native_static_array_element_bytes >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`info`, `abi_static_encoder_size info`, `stride`, `w2n root_addr + 32`, `source_capacity - 32`,
    `ss.vs_memory`, `fields`, `index`] mp_tac abi_native_static_array_prefix >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  qspecl_then [`info`, `dst_addr`, `root_addr`, `abi_static_encoder_size info`, `stride`, `counter_addr`, `labels`, `ss`]
    mp_tac abi_native_static_effect_frame >> impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  asm_simp_tac bool_ss [] >> DISCH_TAC >>
  `read_memory (w2n (root_addr + 32w + mload (w2n counter_addr) ss * n2w stride))
    (abi_static_encoder_size info) ss = SND (EL index fields)` by
    asm_simp_tac bool_ss [read_memory_eq_mem_bytes_at] >>
  qspecl_then [`info`, `dst_addr`, `root_addr`, `stride`, `counter_addr`, `labels`, `SND (EL index fields)`, `ss`]
    mp_tac abi_native_static_array_effect_payload >> impl_tac >- asm_simp_tac bool_ss [] >>
  asm_simp_tac bool_ss [] >> DISCH_TAC >>
  drule_all abi_native_static_array_source_preserved >> strip_tac >>
  drule_all abi_native_static_array_take_step >> DISCH_TAC >>
  qspecl_then [`TAKE index fields`, `SND (EL index fields)`, `w2n dst_addr + 32`, `0`, `abi_field_head_size fields`,
    `[(w2n dst_addr + 32 + index * abi_static_encoder_size info,abi_static_encoder_size info);(w2n counter_addr,32)]`,
    `ss`, `abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss`]
    mp_tac abi_fields_layout_static_extend >>
  impl_tac >- (asm_simp_tac bool_ss [ADD_0] >> simp[abi_window_separated_def]) >> DISCH_TAC >>
  `abi_fields_layout (TAKE (SUC index) fields) (w2n dst_addr + 32) 0 (abi_field_head_size fields)
    (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss)` by
    asm_simp_tac bool_ss [] >>
  `mload (w2n counter_addr)
    (abi_static_loop_effect info dst_addr root_addr (abi_static_encoder_size info) stride counter_addr labels ss) = n2w (SUC index)` by
    simp[abi_static_loop_effect_def, memory_reads_jump_to, abi_static_loop_body_memory_counter, word_add_n2w, ADD1] >>
  PURE_REWRITE_TAC [abi_native_static_array_data_def] >> rpt conj_tac >>
  FIRST [first_assum MATCH_ACCEPT_TAC, decide_tac]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual static runtime iteration memory advancement: " ^ name)
  end) (DB.thms "abiNativeStaticArrayMemory")
