(* TOP-LEVEL: typed static values and length-prefixed bytes/string values
   satisfy the recursive encoder's source-memory relation. The length bounds
   follow from evaluated source types, without a separate runtime premise. *)
Theory abiMemoryTypedLeaf
Ancestors
  abiMemoryEncoding memoryValueAbiStatic memoryValueTyping memoryValueDefs
  valueEncoding vyperABI vyperTyping vyperValue contractABI list words arithmetic

Theorem abi_memory_typed_copy:
  !env ty tv v av source span mem.
    evaluate_type env ty = SOME tv /\
    memory_value_rel tv v source mem /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ ~is_dynamic (vyper_to_abi_type env ty) /\
    type_memory_size tv <= span ==>
    abi_memory_encoding (AbiCopy (type_memory_size tv)) source span mem
      (enc (vyper_to_abi_type env ty) av)
Proof
  rpt strip_tac >> drule_all memory_value_rel_static_abi >> DISCH_TAC >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` (fn th => ONCE_REWRITE_TAC [GSYM th]) >>
  irule abi_memory_encoding_copy >> simp[]
QED

Theorem abi_memory_typed_bytes:
  !env cap bs source span mem.
    evaluate_type env (BaseT (BytesT (Dynamic cap))) = SOME (BaseTV (BytesT (Dynamic cap))) /\
    memory_value_rel (BaseTV (BytesT (Dynamic cap))) (vyperValue$BytesV bs) source mem /\
    value_has_type (BaseTV (BytesT (Dynamic cap))) (vyperValue$BytesV bs) /\
    type_memory_size (BaseTV (BytesT (Dynamic cap))) <= span ==>
    abi_memory_encoding (AbiBytestring cap) source span mem
      (enc (Bytes NONE) (contractABI$BytesV bs))
Proof
  rpt strip_tac >> drule (CONJUNCT1 evaluate_type_well_formed) >> DISCH_TAC >>
  drule value_has_type_val_wf >> DISCH_TAC >> irule abi_memory_encoding_bytes >>
  fs[memory_value_rel_def, val_in_memory_def, val_wf_def,
    well_formed_type_value_def, value_has_type_def] >> decide_tac
QED

Theorem abi_memory_typed_string:
  !env cap s source span mem.
    evaluate_type env (BaseT (StringT cap)) = SOME (BaseTV (StringT cap)) /\
    memory_value_rel (BaseTV (StringT cap)) (StringV s) source mem /\
    value_has_type (BaseTV (StringT cap)) (StringV s) /\
    type_memory_size (BaseTV (StringT cap)) <= span ==>
    abi_memory_encoding (AbiBytestring cap) source span mem
      (enc (Bytes NONE) (contractABI$BytesV (MAP (n2w o ORD) s)))
Proof
  rpt strip_tac >> drule (CONJUNCT1 evaluate_type_well_formed) >> DISCH_TAC >>
  drule value_has_type_val_wf >> DISCH_TAC >> irule abi_memory_encoding_bytes >>
  fs[memory_value_rel_def, val_in_memory_def, val_wf_def,
    well_formed_type_value_def, value_has_type_def] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI memory leaf: " ^ name)
  end) (DB.thms "abiMemoryTypedLeaf")
