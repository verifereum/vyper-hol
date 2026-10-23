(* Heterogeneous canonical bytes and recursive memory predicates. *)
Theory abiStaticListProps
Ancestors abiStaticAggregateProps valueEncoding vyperABI vyperTyping contractABI list

Theorem static_typed_list_memory:
  !tys tvs vs avs off mem.
  LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    (!v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv) /\
    (!v av off mem. value_has_type tv v /\
      vyper_to_abi tenv ty v = SOME av /\
      off + type_memory_size tv <= LENGTH mem /\
      mem_bytes_at off (type_memory_size tv) mem =
        enc (vyper_to_abi_type tenv ty) av ==>
      val_in_memory tv v off mem)) tys tvs /\
  values_have_types tvs vs /\ vyper_to_abi_list tenv tys vs = SOME avs /\
  off + type_memory_size_list tvs <= LENGTH mem /\
  mem_bytes_at off (type_memory_size_list tvs) mem =
    FLAT (MAP2 enc (vyper_to_abi_types tenv tys) avs) ==>
  tuple_in_memory vs tvs off mem
Proof
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, Once vyper_to_abi_def, type_memory_size_def,
       val_in_memory_def] >> rpt gen_tac >> rpt disch_tac >>
  gvs[AllCaseEqs()] >>
  `LIST_REL (\ty tv.
    ~is_dynamic (vyper_to_abi_type tenv ty) /\
    !v av. value_has_type tv v /\ vyper_to_abi tenv ty v = SOME av ==>
      LENGTH (enc (vyper_to_abi_type tenv ty) av) = type_memory_size tv)
    tys t` by
    (qpat_x_assum `LIST_REL _ _ _` mp_tac >>
     match_mp_tac LIST_REL_mono >> simp[] >> metis_tac[]) >>
  drule_all static_typed_list_bss >> strip_tac >>
  `LENGTH (enc (vyper_to_abi_type tenv h'') av) = type_memory_size h` by
    metis_tac[] >>
  conj_tac
  >- (first_x_assum irule >> simp[] >>
      metis_tac[SRULE [] (Q.INST [`pre` |-> `[]`]
        abiStaticPrimitivePropsTheory.mem_bytes_at_child_slice)]) >>
  first_x_assum irule >> simp[] >>
  metis_tac[SRULE [] (Q.INST [`post` |-> `[]`]
    abiStaticPrimitivePropsTheory.mem_bytes_at_child_slice)]
QED

Theorem static_fields_memory_zip:
  !names tvs fs off mem.
  LENGTH names = LENGTH tvs /\ struct_has_type (ZIP(names,tvs)) fs /\
  tuple_in_memory (MAP SND fs) tvs off mem ==>
  fields_in_memory fs (ZIP(names,tvs)) off mem
Proof
  Induct >> Cases_on `tvs` >> Cases_on `fs` >>
  simp[value_has_type_def, val_in_memory_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h'` >> gvs[value_has_type_def, val_in_memory_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_STATIC_LIST_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI static list not kernel closed: " ^ n)
  end) (DB.thms "abiStaticListProps");
