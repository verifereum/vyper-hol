(* TOP-LEVEL: raw static-array sources supply uniform packed output fields
   and each element's bytes at the actual source stride. No equality of
   source stride and encoded width is assumed. *)
Theory abiNativeStaticArraySource
Ancestors
  abiNativeStaticInfo abiMemoryEncoding abiMemoryEncodingElements abiMemoryFieldsLayout abiFieldLayoutDefs
  valueEncoding compileEnv list rich_list pair words arithmetic

Theorem abi_native_static_array_uniform:
  !info width stride source capacity mem fields.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F)) source capacity mem fields ==>
    EVERY (\field. FST field = F /\ LENGTH (SND field) = width) fields
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [EVERY_EL] >> qx_gen_tac `index` >> DISCH_TAC >>
  qspecl_then [`info`, `width`, `stride`, `F`, `source`, `capacity`, `mem`, `fields`, `index`]
    mp_tac abi_memory_array_element >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

Theorem abi_native_uniform_head_size:
  !fields width.
    EVERY (\field. FST field = F /\ LENGTH (SND field) = width) fields ==>
    abi_field_head_size fields = LENGTH fields * width
Proof
  Induct_on `fields` >- simp[abi_field_head_size_def] >>
  simp_tac bool_ss [FORALL_PROD] >> rpt gen_tac >>
  simp_tac (srw_ss()) [EVERY_DEF, abi_field_head_size_def] >> strip_tac >>
  first_x_assum (qspec_then `width` mp_tac) >> simp[MULT_CLAUSES]
QED

Theorem abi_native_static_array_shape:
  !info width stride source capacity mem fields tail_start.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F)) source capacity mem fields ==>
    abi_field_head_size fields = LENGTH fields * width /\ abi_field_tail_size fields = 0 /\
    abi_field_bytes tail_start fields = FLAT (MAP SND fields) /\
    !prefix_len. abi_field_head_size (TAKE prefix_len fields) = MIN prefix_len (LENGTH fields) * width
Proof
  rpt gen_tac >> DISCH_TAC >> drule abi_native_static_array_uniform >> DISCH_TAC >>
  `EVERY (\(flag,payload). ~flag) fields` by
    (fs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >> fs[]) >>
  drule abi_static_field_payloads >> disch_then (qspec_then `tail_start` strip_assume_tac) >>
  drule abi_native_uniform_head_size >> DISCH_TAC >>
  rpt conj_tac >> TRY (first_assum MATCH_ACCEPT_TAC) >> qx_gen_tac `prefix_len` >>
  `EVERY (\field. FST field = F /\ LENGTH (SND field) = width) (TAKE prefix_len fields)` by
    (irule EVERY_TAKE >> first_assum MATCH_ACCEPT_TAC) >>
  `LENGTH (TAKE prefix_len fields) = MIN prefix_len (LENGTH fields)` by
    (simp[LENGTH_TAKE_EQ, MIN_DEF] >> rpt IF_CASES_TAC >> decide_tac) >>
  drule abi_native_uniform_head_size >> simp[]
QED

Theorem abi_native_static_array_element_bytes:
  !info stride source capacity mem fields index.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,abi_static_encoder_size info,stride,F))
      source capacity mem fields /\ index < LENGTH fields ==>
    FST (EL index fields) = F /\ LENGTH (SND (EL index fields)) = abi_static_encoder_size info /\
    mem_bytes_at (source + index * stride) (abi_static_encoder_size info) mem = SND (EL index fields)
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_array_element >> simp_tac bool_ss [] >> strip_tac >>
  qspecl_then [`info`, `source + index * stride`, `stride`, `mem`, `SND (EL index fields)`]
    mp_tac abi_memory_static_payload >> impl_tac >- asm_simp_tac bool_ss [] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed raw stride-aware static array source: " ^ name)
  end) (DB.thms "abiNativeStaticArraySource")
