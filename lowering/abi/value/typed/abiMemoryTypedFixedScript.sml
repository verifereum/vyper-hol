(* TOP-LEVEL: the compiler's fixed-array descriptor encodes arbitrary
   dynamic children in sparse source arrays, including default-filled holes. *)
Theory abiMemoryTypedFixed
Ancestors
  abiMemoryTypedDefs abiMemoryTypedMetadata abiMemoryTypedArray abiMemoryTypedArraySource
  abiMemoryTypedSparse abiMemoryTypedBase abiMemoryEncoding abiTypeShape
  memoryValueDefs exprLowering compileEnv valueEncoding vyperABI vyperValue
  vyperTyping vyperTypeValues contractABI list rich_list pair combin arithmetic

Theorem abi_memory_typed_fixed_array:
  !env sfields cenv ty tv array_count sparse avs source span mem.
    abi_memory_env_rel env cenv /\
    abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty) /\
    evaluate_type env ty = SOME tv /\ is_dynamic (vyper_to_abi_type env ty) /\
    memory_value_rel (ArrayTV tv (Fixed array_count)) (ArrayV (SArrayV sparse)) source mem /\
    sparse_has_type tv array_count sparse /\ vyper_to_abi_sparse env ty tv array_count sparse = SOME avs /\
    array_count * type_memory_size tv <= span ==>
    abi_memory_encoding (type_to_abi_enc_info sfields cenv (ArrayT ty (Fixed array_count)))
      source span mem (enc (Array (SOME array_count) (vyper_to_abi_type env ty)) (ListV avs))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`env`, `sfields`, `cenv`, `ty`, `tv`] mp_tac abi_typed_element_metadata >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`env`, `ty`, `tv`, `type_to_abi_enc_info sfields cenv ty`,
    `sparse`, `array_count`, `avs`, `source`, `mem`] mp_tac abi_typed_memory_sparse_elements >>
  impl_tac >- simp[] >> strip_tac >>
  `is_abi_dynamic cenv.ce_struct_fields (ArrayT ty (Fixed array_count))` by
    simp[Once is_abi_dynamic_def] >>
  `EVERY (\av. ~is_dynamic (vyper_to_abi_type env ty) ==>
    LENGTH (enc (vyper_to_abi_type env ty) av) = static_length (vyper_to_abi_type env ty)) avs` by simp[] >>
  drule_then (qspec_then `SOME array_count` mp_tac) enc_array_field_bytes >>
  simp_tac list_ss [] >> disch_then SUBST1_TAC >>
  asm_simp_tac bool_ss [Once type_to_abi_enc_info_def, GSYM REPLICATE_GENLIST] >>
  irule abi_memory_encoding_complex >>
  qspecl_then [`vyper_to_abi_type env ty`, `avs`, `type_to_abi_enc_info sfields cenv ty`,
    `32`, `type_memory_size tv`, `T`, `source`, `span`, `mem`]
    mp_tac abi_memory_typed_array_elements >> simp[]
QED

Theorem abi_typed_memory_fixed_array:
  !env sfields cenv ty array_count.
    abi_memory_env_rel env cenv /\
    abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty) ==>
    abi_typed_memory env (ArrayT ty (Fixed array_count))
      (type_to_abi_enc_info sfields cenv (ArrayT ty (Fixed array_count)))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (PURE_REWRITE_TAC [abi_typed_memory_def] >> rpt gen_tac >> strip_tac >>
      drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
      Cases_on `v` >> gvs[value_has_type_def] >>
      rename1 `ArrayV array_value` >> Cases_on `array_value` >> gvs[value_has_type_def] >>
      gvs[AllCaseEqs()] >> simp_tac bool_ss [Once vyper_to_abi_type_def] >>
      rename1 `evaluate_type env ty = SOME elem_tv` >>
      rename1 `vyper_to_abi_sparse env ty elem_tv array_count sparse = SOME avs` >>
      qspecl_then [`env`, `sfields`, `cenv`, `ty`, `elem_tv`, `array_count`, `sparse`, `avs`,
        `source`, `span`, `mem`] mp_tac abi_memory_typed_fixed_array >>
      fs[type_memory_size_def]) >>
  irule abi_typed_memory_static >> simp[Once vyper_to_abi_type_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI fixed array: " ^ name)
  end) (DB.thms "abiMemoryTypedFixed")
