(* TOP-LEVEL: identical struct metadata reduces the actual named-field
   copier to the verified sequential tuple-field copier. Field lookup and
   stored strides are justified explicitly, including list suffixes. *)
Theory typedStructCode
Ancestors
  context compileEnv list alist pair combin

Theorem struct_field_self_lookup:
  !fields name ty byte_count.
    ALL_DISTINCT (MAP FST fields) /\ MEM (name,ty,byte_count) fields ==>
    ALOOKUP fields name = SOME (ty,byte_count)
Proof
  rpt gen_tac >> strip_tac >> irule ALOOKUP_ALL_DISTINCT_MEM >> simp[]
QED

Theorem compile_typed_struct_dispatch:
  !cenv dst src dst_id src_id.
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    compile_store_memory_typed cenv dst (StructT dst_id) src (StructT src_id) =
    compile_struct_typed_copy cenv dst src
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string dst_id))
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string src_id)) 0 0
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def, LET_THM]
QED

Theorem compile_struct_typed_copy_fields:
  !fields cenv dst src source_fields dst_off src_off.
    (!name ty byte_count. MEM (name,ty,byte_count) fields ==>
      ALOOKUP source_fields name = SOME (ty,byte_count) /\
      byte_count = type_memory_bytes cenv ty) ==>
    compile_struct_typed_copy cenv dst src fields source_fields dst_off src_off =
    compile_typed_copy_fields cenv dst src (MAP (FST o SND) fields) (MAP (FST o SND) fields) dst_off src_off
Proof
  Induct_on `fields`
  >- (simp[Once compile_store_memory_typed_def] >> simp[Once compile_store_memory_typed_def]) >>
  MAP_EVERY qx_gen_tac [`entry`, `cenv`, `dst`, `src`, `source_fields`, `dst_off`, `src_off`] >>
  PairCases_on `entry` >> rename1 `(name,ty,byte_count)::fields` >> DISCH_TAC >>
  `ALOOKUP source_fields name = SOME (ty,byte_count) /\ byte_count = type_memory_bytes cenv ty` by
    (first_x_assum irule >> simp[]) >>
  `compile_struct_typed_copy cenv dst src fields source_fields
      (dst_off + type_memory_bytes cenv ty) (src_off + type_memory_bytes cenv ty) =
    compile_typed_copy_fields cenv dst src (MAP (FST o SND) fields) (MAP (FST o SND) fields)
      (dst_off + type_memory_bytes cenv ty) (src_off + type_memory_bytes cenv ty)` by
    (first_x_assum irule >> rpt gen_tac >> DISCH_TAC >> first_x_assum irule >> simp[]) >>
  simp_tac (srw_ss()) [o_DEF] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [compile_store_memory_typed_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [compile_store_memory_typed_def])) >>
  asm_simp_tac (srw_ss()) [LET_THM, o_DEF]
QED

Theorem compile_struct_typed_copy_identical:
  !cenv dst src fields dst_off src_off.
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\entry. SND (SND entry) = type_memory_bytes cenv (FST (SND entry))) fields ==>
    compile_struct_typed_copy cenv dst src fields fields dst_off src_off =
    compile_typed_copy_fields cenv dst src (MAP (FST o SND) fields) (MAP (FST o SND) fields) dst_off src_off
Proof
  rpt gen_tac >> strip_tac >> irule compile_struct_typed_copy_fields >>
  MAP_EVERY qx_gen_tac [`name`, `ty`, `byte_count`] >> DISCH_TAC >> conj_tac
  >- (irule struct_field_self_lookup >> simp[]) >> fs[EVERY_MEM] >>
  qpat_x_assum `!entry. MEM entry fields ==> _` (qspec_then `(name,ty,byte_count)` mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual struct field copy reduction: " ^ name)
  end) (DB.thms "typedStructCode")
