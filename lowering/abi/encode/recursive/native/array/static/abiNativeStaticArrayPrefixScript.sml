(* TOP-LEVEL: a live static-array index extends the completed packed
   prefix by exactly its selected field. Prefix tails are empty. *)
Theory abiNativeStaticArrayPrefix
Ancestors
  abiNativeStaticArraySource abiMemoryEncoding abiMemoryFieldsLayout abiFieldLayoutDefs
  compileEnv list rich_list pair arithmetic

Theorem abi_native_static_array_prefix:
  !info width stride source capacity mem fields index.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F)) source capacity mem fields /\
    index <= LENGTH fields ==>
    abi_field_head_size (TAKE index fields) = index * width /\ abi_field_tail_size (TAKE index fields) = 0
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`info`, `width`, `stride`, `source`, `capacity`, `mem`, `fields`, `0`]
    mp_tac abi_native_static_array_shape >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  `MIN index (LENGTH fields) = index` by (simp[MIN_DEF] >> IF_CASES_TAC >> decide_tac) >>
  qpat_x_assum `!prefix_len. _` (qspec_then `index` ASSUME_TAC) >>
  drule abi_native_static_array_uniform >> DISCH_TAC >>
  `EVERY (\(flag,payload). ~flag) fields` by
    (fs[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >> fs[]) >>
  `EVERY (\(flag,payload). ~flag) (TAKE index fields)` by (irule EVERY_TAKE >> first_assum MATCH_ACCEPT_TAC) >>
  qspecl_then [`TAKE index fields`, `0`] mp_tac abi_static_field_payloads >> impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  simp[]
QED

Theorem abi_native_static_array_take_step:
  !info width stride source capacity mem fields index.
    abi_memory_fields (REPLICATE (LENGTH fields) (info,width,stride,F)) source capacity mem fields /\
    index < LENGTH fields ==>
    TAKE (SUC index) fields = TAKE index fields ++ [(F,SND (EL index fields))]
Proof
  rpt gen_tac >> strip_tac >> drule abi_native_static_array_uniform >> DISCH_TAC >>
  `FST (EL index fields) = F` by fs[EVERY_EL] >>
  `EL index fields = (F,SND (EL index fields))` by (Cases_on `EL index fields` >> fs[]) >>
  simp[TAKE_SUC_BY_TAKE, SNOC_APPEND]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed packed static runtime array prefix: " ^ name)
  end) (DB.thms "abiNativeStaticArrayPrefix")
