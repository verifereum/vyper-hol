(* TOP-LEVEL: static traversal aligns the semantic child induction
   assertions with the same remaining payloads used by the runtime layout.
   The parent has no physical counter; its dummy operand is Lit 0w. *)
Theory abiNativeStaticState
Ancestors
  abiNativeFields abiNativeEncodingDefs abiMemoryStaticFieldsState abiMemoryFieldsLayout
  abiMemoryFieldsState abiMemoryFieldEntry abiMemoryEncoding abiFieldMemory abiFieldLayoutDefs
  compileEnv venomState list pair words arithmetic

Definition abi_native_static_state_def:
  abi_native_static_state full dst src dst_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss <=>
    EVERY (\(is_dyn,payload). ~is_dyn) full /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss /\
    ?done remaining. full = done ++ remaining /\ head_offset = abi_field_head_size done /\
      abi_memory_fields_layout done entries remaining (abi_field_head_size full)
        dst_addr root_addr source_capacity source_offset ss /\
      abi_native_fields entries (w2n root_addr + source_offset) reference remaining
End

Theorem abi_native_static_initial:
  !full dst src dst_addr root_addr source_capacity reference entries cs ss.
    ~EXISTS (\(_,_,_,flag). flag) entries /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss /\
    w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields entries (w2n root_addr) source_capacity ss.vs_memory full /\
    abi_native_fields entries (w2n root_addr) reference full ==>
    abi_native_static_state full dst src dst_addr root_addr source_capacity reference entries 0 0 cs ss
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_fields_static_flags >> DISCH_TAC >>
  simp_tac bool_ss [abi_native_static_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`[]`, `full`] >>
  simp[abi_memory_fields_layout_initial, abi_field_head_size_def]
QED

Theorem abi_native_static_memory_state:
  !full dst src dst_addr root_addr source_capacity reference entries source_offset head_offset cs ss.
    abi_native_static_state full dst src dst_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss ==>
    abi_memory_static_fields_state full dst src dst_addr root_addr source_capacity
      entries source_offset head_offset cs ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_static_state_def] >> strip_tac >>
  rename1 `full = done ++ remaining` >>
  qspecl_then [`full`, `done`, `remaining`, `dst`, `src`, `dst_addr`, `root_addr`,
    `source_capacity`, `entries`, `source_offset`, `head_offset`, `cs`, `ss`]
    mp_tac abi_memory_static_fields_intro >> simp[]
QED

Theorem abi_native_static_intro:
  !full done remaining dst src dst_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss.
    EVERY (\(is_dyn,payload). ~is_dyn) full /\ full = done ++ remaining /\
    head_offset = abi_field_head_size done /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss /\
    abi_memory_fields_layout done entries remaining (abi_field_head_size full)
      dst_addr root_addr source_capacity source_offset ss /\
    abi_native_fields entries (w2n root_addr + source_offset) reference remaining ==>
    abi_native_static_state full dst src dst_addr root_addr source_capacity reference
      entries source_offset head_offset cs ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_native_static_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`done`, `remaining`] >> simp[]
QED

Theorem abi_native_static_current:
  !full dst src dst_addr root_addr source_capacity reference info abi_sz mem_sz is_dyn rest
      source_offset head_offset cs ss.
    abi_native_static_state full dst src dst_addr root_addr source_capacity reference
      ((info,abi_sz,mem_sz,is_dyn)::rest) source_offset head_offset cs ss ==>
    is_dyn = F /\ ?done payload fields.
      full = done ++ ((F,payload)::fields) /\ head_offset = abi_field_head_size done /\
      abi_memory_fields_layout done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
        (abi_field_head_size full) dst_addr root_addr source_capacity source_offset ss /\
      abi_native_fields ((info,abi_sz,mem_sz,F)::rest)
        (w2n root_addr + source_offset) reference ((F,payload)::fields)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_native_static_state_def, abi_memory_fields_layout_def] >>
  strip_tac >>
  qpat_x_assum `abi_memory_fields ((info,abi_sz,mem_sz,is_dyn)::rest) _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Once abi_memory_fields_cases] >> strip_tac >> gvs[EVERY_APPEND] >>
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
    then () else raise Fail ("unclosed aligned native static traversal state: " ^ name)
  end) (DB.thms "abiNativeStaticState")
