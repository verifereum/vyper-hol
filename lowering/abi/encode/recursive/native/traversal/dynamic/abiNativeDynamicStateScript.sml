(* TOP-LEVEL: mixed static/dynamic traversal aligns semantic child
   assertions with the runtime source suffix, head/tail layout and cursor. *)
Theory abiNativeDynamicState
Ancestors
  abiNativeFields abiMemoryFieldsState abiMemoryFieldEntry abiMemoryEncoding
  abiFieldMemory abiFieldLayoutDefs compileEnv venomState list pair words arithmetic

Definition abi_native_dynamic_state_def:
  abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss <=>
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    ?done remaining. full = done ++ remaining /\ head_offset = abi_field_head_size done /\
      abi_memory_fields_data done entries remaining (abi_field_head_size full)
        dst_addr dyn_addr root_addr source_capacity source_offset ss /\
      abi_native_fields entries (w2n root_addr + source_offset) reference remaining
End

Theorem abi_native_dynamic_initial:
  !full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference entries cs ss.
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields entries (w2n root_addr) source_capacity ss.vs_memory full /\
    abi_native_fields entries (w2n root_addr) reference full /\
    mload (w2n dyn_addr) ss = n2w (abi_field_head_size full) ==>
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      entries 0 0 cs ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_native_dynamic_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`[]`, `full`] >>
  simp[abi_memory_fields_data_def, abi_field_head_size_def]
QED

Theorem abi_native_dynamic_memory_state:
  !full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss.
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss ==>
    abi_memory_fields_state full dst src dyn_ptr (abi_field_head_size full) dst_addr dyn_addr root_addr
      source_capacity entries source_offset head_offset cs ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_dynamic_state_def] >> strip_tac >>
  rename1 `full = done ++ remaining` >>
  qspecl_then [`full`, `done`, `remaining`, `dst`, `src`, `dyn_ptr`, `abi_field_head_size full`,
    `dst_addr`, `dyn_addr`, `root_addr`, `source_capacity`, `entries`, `source_offset`, `head_offset`, `cs`, `ss`]
    mp_tac abi_memory_fields_state_intro >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]
QED

Theorem abi_native_dynamic_intro:
  !full done remaining dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss.
    full = done ++ remaining /\ head_offset = abi_field_head_size done /\
    abi_memory_fields_operands dst src dyn_ptr dst_addr root_addr dyn_addr cs ss /\
    abi_memory_fields_data done entries remaining (abi_field_head_size full)
      dst_addr dyn_addr root_addr source_capacity source_offset ss /\
    abi_native_fields entries (w2n root_addr + source_offset) reference remaining ==>
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_native_dynamic_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`done`, `remaining`] >> simp[]
QED

Theorem abi_native_dynamic_current:
  !full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference info abi_sz mem_sz is_dyn rest
      source_offset head_offset cs ss.
    abi_native_dynamic_state full dst src dyn_ptr dst_addr dyn_addr root_addr source_capacity reference
      ((info,abi_sz,mem_sz,is_dyn)::rest) source_offset head_offset cs ss ==>
    ?done payload fields.
      full = done ++ ((is_dyn,payload)::fields) /\ head_offset = abi_field_head_size done /\
      abi_memory_fields_data done ((info,abi_sz,mem_sz,is_dyn)::rest) ((is_dyn,payload)::fields)
        (abi_field_head_size full) dst_addr dyn_addr root_addr source_capacity source_offset ss /\
      abi_native_fields ((info,abi_sz,mem_sz,is_dyn)::rest)
        (w2n root_addr + source_offset) reference ((is_dyn,payload)::fields)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_dynamic_state_def, abi_memory_fields_data_def] >> strip_tac >>
  qpat_x_assum `abi_memory_fields ((info,abi_sz,mem_sz,is_dyn)::rest) _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Once abi_memory_fields_cases] >> strip_tac >> gvs[] >>
  rename1 `abi_fields_layout done _ _ _ ss` >>
  rename1 `abi_memory_encoding info _ mem_sz _ payload` >>
  rename1 `abi_memory_fields rest _ _ _ fields` >>
  qexistsl_tac [`done`, `payload`, `fields`] >> simp[] >>
  simp_tac bool_ss [abi_memory_fields_cons_cases] >> asm_simp_tac bool_ss [] >>
  `(source_offset + w2n root_addr) + mem_sz = mem_sz + (source_offset + w2n root_addr)` by decide_tac >>
  `source_capacity - source_offset - mem_sz = source_capacity - (mem_sz + source_offset)` by decide_tac >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed aligned native dynamic traversal state: " ^ name)
  end) (DB.thms "abiNativeDynamicState")
