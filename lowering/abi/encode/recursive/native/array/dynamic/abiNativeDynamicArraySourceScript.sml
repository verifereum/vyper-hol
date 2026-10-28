(* TOP-LEVEL: raw dynamic-child arrays have word-sized heads and separate
   variable-sized tails. Each runtime index extends the packed prefix by
   exactly its selected child payload at the independent source stride. *)
Theory abiNativeDynamicArraySource
Ancestors
  abiMemoryEncoding abiMemoryEncodingElements abiNativeDynamicBounds abiFieldLayoutDefs compileEnv list rich_list pair words arithmetic

Theorem abi_native_dynamic_array_flags:
  !info width stride source capacity mem fields.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) source capacity mem fields ==>
    EVERY FST fields
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [EVERY_EL] >> qx_gen_tac `index` >> DISCH_TAC >>
  qspecl_then [`info`, `width`, `stride`, `T`, `source`, `capacity`, `mem`, `fields`, `index`]
    mp_tac abi_memory_array_element >> impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

Theorem abi_native_dynamic_heads:
  !fields. EVERY FST fields ==> abi_field_head_size fields = LENGTH fields * 32
Proof
  Induct_on `fields` >- simp[abi_field_head_size_def] >>
  simp_tac bool_ss [FORALL_PROD] >> rpt gen_tac >>
  simp_tac (srw_ss()) [EVERY_DEF, abi_field_head_size_def] >> strip_tac >>
  first_x_assum drule >> simp[MULT_CLAUSES]
QED

Theorem abi_native_dynamic_array_shape:
  !info width stride source capacity mem fields.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) source capacity mem fields ==>
    abi_field_head_size fields = LENGTH fields * width /\
    !index. abi_field_head_size (TAKE index fields) = MIN index (LENGTH fields) * 32
Proof
  rpt gen_tac >> DISCH_TAC >> drule abi_memory_fields_head_size >> simp[] >> DISCH_TAC >>
  drule abi_native_dynamic_array_flags >> DISCH_TAC >>
  qx_gen_tac `index` >> `EVERY FST (TAKE index fields)` by (irule EVERY_TAKE >> first_assum MATCH_ACCEPT_TAC) >>
  drule abi_native_dynamic_heads >> DISCH_TAC >>
  `LENGTH (TAKE index fields) = MIN index (LENGTH fields)` by
    (simp[LENGTH_TAKE_EQ, MIN_DEF] >> rpt IF_CASES_TAC >> decide_tac) >> simp[]
QED

Theorem abi_native_dynamic_array_take_step:
  !info width stride source capacity mem fields index.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) source capacity mem fields /\
    index < LENGTH fields ==>
    FST (EL index fields) = T /\ width = 32 /\
    abi_memory_encoding info (source + index * stride) stride mem (SND (EL index fields)) /\
    TAKE (SUC index) fields = TAKE index fields ++ [(T,SND (EL index fields))] /\
    abi_field_tail_size (TAKE (SUC index) fields) =
      abi_field_tail_size (TAKE index fields) + LENGTH (SND (EL index fields))
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_memory_array_element >> simp_tac bool_ss [] >> strip_tac >>
  `EL index fields = (T,SND (EL index fields))` by (Cases_on `EL index fields` >> fs[]) >>
  `TAKE (SUC index) fields = TAKE index fields ++ [(T,SND (EL index fields))]` by
    simp[TAKE_SUC_BY_TAKE, SNOC_APPEND] >>
  asm_simp_tac (srw_ss()) [abi_field_tail_size_append, abi_field_tail_def]
QED

Theorem abi_native_dynamic_array_ranges:
  !info width stride source capacity mem fields index.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,T)) source capacity mem fields /\
    index < LENGTH fields ==>
    abi_field_head_size (TAKE index fields) + 32 <= abi_field_head_size fields /\
    abi_field_tail_size (TAKE index fields) + LENGTH (SND (EL index fields)) <= abi_field_tail_size fields
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_dynamic_array_take_step >> strip_tac >>
  `fields = TAKE index fields ++ ((T,SND (EL index fields))::DROP (SUC index) fields)` by
    (qpat_assum `TAKE (SUC index) fields = _` (fn take_th =>
       qspecl_then [`SUC index`, `fields`]
         (ACCEPT_TAC o SYM o SIMP_RULE bool_ss [take_th, GSYM APPEND_ASSOC, APPEND]) TAKE_DROP)) >>
  qspecl_then [`fields`, `TAKE index fields`, `T`, `SND (EL index fields)`, `DROP (SUC index) fields`]
    mp_tac abi_native_field_ranges >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp_tac bool_ss []
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed raw dynamic-child array heads and tail prefixes: " ^ name)
  end) (DB.thms "abiNativeDynamicArraySource")
