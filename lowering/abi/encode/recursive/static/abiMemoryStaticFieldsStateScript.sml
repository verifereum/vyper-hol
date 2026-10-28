(* TOP-LEVEL: the actual all-static aggregate traversal keeps source and
   completed output at each compiler cut. Its Lit 0w argument is only an
   operand; no memory cell at address zero is assumed to hold a cursor.
   Child payloads may come from arbitrary recursive encoder metadata. *)
Theory abiMemoryStaticFieldsState
Ancestors
  abiMemoryFieldsLayout abiMemoryFieldsState abiMemoryEncoding abiMemoryEncodingElements
  abiMemoryFieldEntry abiFieldMemory
  abiFieldLayoutDefs abiFieldOperands compileEnv venomState list pair words arithmetic

Definition abi_memory_static_fields_state_def:
  abi_memory_static_fields_state full dst src dst_addr root_addr source_capacity
      entries source_offset head_offset cs ss <=>
    EVERY (\(is_dyn,payload). ~is_dyn) full /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss /\
    ?done remaining. full = done ++ remaining /\ head_offset = abi_field_head_size done /\
      abi_memory_fields_layout done entries remaining (abi_field_head_size full)
        dst_addr root_addr source_capacity source_offset ss
End

Theorem abi_memory_fields_static_flags:
  !entries src span mem full.
    abi_memory_fields entries src span mem full /\
    ~EXISTS (\(_,_,_,flag). flag) entries ==>
    EVERY (\(is_dyn,payload). ~is_dyn) full
Proof
  rpt gen_tac >> strip_tac >> drule abi_memory_fields_flags >> DISCH_TAC >>
  `EVERY (\flag. ~flag) (MAP (\(_,_,_,flag). flag) entries)` by
    fs[NOT_EXISTS, EVERY_MAP, combinTheory.o_DEF] >>
  `EVERY (\flag. ~flag) (MAP FST full)` by simp[] >>
  fs[EVERY_MAP, EVERY_MEM, FORALL_PROD, combinTheory.o_DEF]
QED

Theorem abi_memory_static_fields_initial:
  !full dst src dst_addr root_addr source_capacity entries cs ss.
    ~EXISTS (\(_,_,_,flag). flag) entries /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss /\
    w2n root_addr + source_capacity < dimword (:256) /\
    abi_memory_fields entries (w2n root_addr) source_capacity ss.vs_memory full ==>
    abi_memory_static_fields_state full dst src dst_addr root_addr source_capacity entries 0 0 cs ss
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_fields_static_flags >> DISCH_TAC >>
  simp_tac bool_ss [abi_memory_static_fields_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`[]`, `full`] >>
  simp[abi_memory_fields_layout_initial, abi_field_head_size_def]
QED

Theorem abi_memory_static_fields_intro:
  !full done remaining dst src dst_addr root_addr source_capacity entries source_offset head_offset cs ss.
    EVERY (\(is_dyn,payload). ~is_dyn) full /\
    full = done ++ remaining /\ head_offset = abi_field_head_size done /\
    abi_memory_fields_operands dst src (Lit 0w) dst_addr root_addr 0w cs ss /\
    abi_memory_fields_layout done entries remaining (abi_field_head_size full)
      dst_addr root_addr source_capacity source_offset ss ==>
    abi_memory_static_fields_state full dst src dst_addr root_addr source_capacity
      entries source_offset head_offset cs ss
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_memory_static_fields_state_def] >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >>
  conj_tac >- first_assum MATCH_ACCEPT_TAC >> qexistsl_tac [`done`, `remaining`] >> simp[]
QED

Theorem abi_memory_static_fields_current:
  !full dst src dst_addr root_addr source_capacity info abi_sz mem_sz is_dyn rest
      source_offset head_offset cs ss.
    abi_memory_static_fields_state full dst src dst_addr root_addr source_capacity
      ((info,abi_sz,mem_sz,is_dyn)::rest) source_offset head_offset cs ss ==>
    is_dyn = F /\ ?done payload fields.
      full = done ++ ((F,payload)::fields) /\ head_offset = abi_field_head_size done /\
      abi_memory_fields_layout done ((info,abi_sz,mem_sz,F)::rest) ((F,payload)::fields)
        (abi_field_head_size full) dst_addr root_addr source_capacity source_offset ss
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_static_fields_state_def, abi_memory_fields_layout_def] >>
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

Theorem abi_memory_static_fields_complete:
  !full dst src dst_addr root_addr source_capacity source_offset head_offset cs ss.
    abi_memory_static_fields_state full dst src dst_addr root_addr source_capacity
      [] source_offset head_offset cs ss ==>
    read_memory (w2n dst_addr) (LENGTH (abi_field_bytes (abi_field_head_size full) full)) ss =
      abi_field_bytes (abi_field_head_size full) full /\
    head_offset = abi_field_head_size full /\
    head_offset = LENGTH (abi_field_bytes (abi_field_head_size full) full)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_static_fields_state_def] >> strip_tac >>
  rename1 `full = done ++ remaining` >>
  `remaining = []` by
    (fs[abi_memory_fields_layout_def] >> drule abi_memory_fields_length >> simp[]) >> gvs[] >>
  rename1 `abi_memory_fields_layout finished [] [] _ _ _ _ _ ss` >>
  `abi_field_tail_size finished = 0` by
    (qspecl_then [`finished`, `abi_field_head_size finished`] mp_tac abi_static_field_payloads >>
     impl_tac >- simp[] >> simp[]) >>
  drule abi_memory_fields_layout_complete >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native static aggregate traversal state: " ^ name)
  end) (DB.thms "abiMemoryStaticFieldsState")
