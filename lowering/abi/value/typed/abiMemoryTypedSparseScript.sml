(* TOP-LEVEL: a complete sparse fixed array supplies every default-filled
   child value to the recursive ABI source relation. *)
Theory abiMemoryTypedSparse
Ancestors
  abiMemoryTypedDefs abiMemoryTypedElements sourceAbiArray memoryValueAbiArray
  memoryValueDefs valueEncoding vyperABI vyperValue vyperValueOperation vyperTyping
  vyperAssignPreservesType contractABI list rich_list alist arithmetic

Theorem abi_typed_memory_sparse_elements:
  !env ty tv info sparse array_count avs source mem.
    abi_typed_memory env ty info /\ evaluate_type env ty = SOME tv /\
    sparse_has_type tv array_count sparse /\
    memory_value_rel (ArrayTV tv (Fixed array_count)) (ArrayV (SArrayV sparse)) source mem /\
    vyper_to_abi_sparse env ty tv array_count sparse = SOME avs ==>
    LENGTH avs = array_count /\
    (!i. i < array_count ==>
      abi_memory_encoding info (source + i * type_memory_size tv) (type_memory_size tv) mem
        (enc (vyper_to_abi_type env ty) (EL i avs))) /\
    EVERY (\av. ~is_dynamic (vyper_to_abi_type env ty) ==>
      LENGTH (enc (vyper_to_abi_type env ty) av) = type_memory_size tv) avs
Proof
  rpt gen_tac >> strip_tac >>
  `vyper_to_abi_same env ty (array_elements (ArrayTV tv (Fixed array_count)) (SArrayV sparse)) = SOME avs` by
    (drule_then (qspecl_then [`array_count`, `sparse`] mp_tac) vyper_to_abi_sparse_elements >> simp[]) >>
  `all_have_type tv (array_elements (ArrayTV tv (Fixed array_count)) (SArrayV sparse))` by
    (simp[all_have_type_EVERY, EVERY_EL, array_elements_def, EL_GENLIST] >>
     qx_gen_tac `i` >> DISCH_TAC >>
     qspecl_then [`env`, `ty`, `tv`, `sparse`, `array_count`, `i`]
       mp_tac sparse_slot_has_type >> simp[]) >>
  qspecl_then [`env`, `ty`, `tv`, `info`,
    `array_elements (ArrayTV tv (Fixed array_count)) (SArrayV sparse)`, `avs`, `source`, `mem`]
    mp_tac abi_typed_memory_elements >>
  impl_tac >- fs[memory_value_rel_def, array_elements_def] >> simp[array_elements_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI sparse array: " ^ name)
  end) (DB.thms "abiMemoryTypedSparse")
