(* TOP-LEVEL: contracts connecting evaluated source values and complete
   memory layouts to recursive ABI encoder metadata. The field contract
   follows the source tuple layout and its actual ABI head/tail encoding. *)
Theory abiMemoryTypedDefs
Ancestors
  abiMemoryEncoding memoryValueDefs valueEncoding vyperABI vyperTyping
  vyperValue contractABI list

Definition abi_typed_memory_def:
  abi_typed_memory env ty info <=>
    !tv v av source span mem.
      evaluate_type env ty = SOME tv /\
      memory_value_rel tv v source mem /\ value_has_type tv v /\
      vyper_to_abi env ty v = SOME av /\ type_memory_size tv <= span ==>
      abi_memory_encoding info source span mem (enc (vyper_to_abi_type env ty) av)
End

Definition abi_typed_fields_def:
  abi_typed_fields env tys entries <=>
    !tvs vs avs source span mem.
      LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
      memory_tuple_rel tvs vs source mem /\ values_have_types tvs vs /\
      vyper_to_abi_list env tys vs = SOME avs /\ type_memory_size_list tvs <= span ==>
      abi_memory_fields entries source span mem
        (MAP2 (\ty av. (is_dynamic ty, enc ty av)) (MAP (vyper_to_abi_type env) tys) avs)
End

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI memory contract: " ^ name)
  end) (DB.thms "abiMemoryTypedDefs")
