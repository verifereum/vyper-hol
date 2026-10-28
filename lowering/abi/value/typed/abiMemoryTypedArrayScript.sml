(* TOP-LEVEL: the actual compiler's dynamic-array descriptor encodes every
   typed live element, including arbitrary recursively nested aggregates.
   Helpers derive metadata and length bounds from evaluated source types. *)
Theory abiMemoryTypedArray
Ancestors
  abiMemoryTypedDefs abiMemoryTypedMetadata abiMemoryTypedElements abiMemoryTypedArraySource
  abiMemoryEncoding abiTypeShape abiTypeWidths sourceAbiStaticWidth typedArrayLoopValues
  memoryValueDefs memoryValueAbiStatic exprLowering compileEnv valueEncoding
  vyperABI vyperValue vyperTyping vyperTypeValues vyperAssignPreservesType
  contractABI list rich_list pair words arithmetic

Theorem abi_typed_element_metadata:
  !env sfields cenv ty tv.
    abi_memory_env_rel env cenv /\ evaluate_type env ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv /\
    is_abi_dynamic cenv.ce_struct_fields ty = is_dynamic (vyper_to_abi_type env ty) /\
    abi_embedded_static_size cenv.ce_struct_fields ty =
      (if is_dynamic (vyper_to_abi_type env ty) then 32 else type_memory_size tv) /\
    (~is_dynamic (vyper_to_abi_type env ty) ==>
      abi_embedded_static_size cenv.ce_struct_fields ty =
        abi_static_encoder_size (type_to_abi_enc_info sfields cenv ty))
Proof
  rpt gen_tac >> strip_tac >>
  `abi_struct_env_rel env cenv.ce_struct_fields /\
   type_memory_bytes cenv ty = type_memory_size tv` by
    (fs[abi_memory_env_rel_def] >> first_x_assum drule_all >> simp[]) >>
  drule_all (CONJUNCT1 abi_type_dynamic_joint) >> DISCH_TAC >>
  drule_all evaluated_abi_embedded_width >> DISCH_TAC >> simp[] >>
  strip_tac >> drule_all evaluated_static_encoder_size >> simp[]
QED

Theorem abi_memory_typed_dynamic_array:
  !env sfields cenv ty tv cap vs avs source span mem.
    abi_memory_env_rel env cenv /\
    abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty) /\
    evaluate_type env (ArrayT ty (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
    memory_value_rel (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) source mem /\
    value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
    vyper_to_abi_same env ty vs = SOME avs /\
    type_memory_size (ArrayTV tv (Dynamic cap)) <= span ==>
    abi_memory_encoding (type_to_abi_enc_info sfields cenv (ArrayT ty (Dynamic cap)))
      source span mem (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))
Proof
  rpt gen_tac >> strip_tac >> drule evaluate_type_dynarray_count_bound >> strip_tac >>
  qspecl_then [`env`, `sfields`, `cenv`, `ty`, `tv`] mp_tac abi_typed_element_metadata >>
  impl_tac >- simp[] >> strip_tac >>
  `all_have_type tv vs /\ LENGTH vs <= cap` by fs[value_has_type_def] >>
  qspecl_then [`env`, `ty`, `tv`, `type_to_abi_enc_info sfields cenv ty`,
    `vs`, `avs`, `source + 32`, `mem`] mp_tac abi_typed_memory_elements >>
  impl_tac >- fs[memory_value_rel_def] >> strip_tac >>
  qpat_x_assum `memory_value_rel (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) source mem`
    (strip_assume_tac o ONCE_REWRITE_RULE [memory_value_rel_def]) >>
  qpat_x_assum `LENGTH avs = LENGTH vs`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th])) >>
  `LENGTH avs * type_memory_size tv <= cap * type_memory_size tv` by simp[LE_MULT_RCANCEL] >>
  `32 + LENGTH avs * type_memory_size tv <= span` by
    (qpat_x_assum `type_memory_size (ArrayTV tv (Dynamic cap)) <= span` mp_tac >>
     simp_tac bool_ss [type_memory_size_def] >> decide_tac) >>
  `LENGTH avs < dimword (:256)` by decide_tac >>
  `~is_dynamic (vyper_to_abi_type env ty) ==>
   type_memory_size tv = static_length (vyper_to_abi_type env ty)` by
    (strip_tac >> drule_all (CONJUNCT1 source_abi_static_width) >> simp[]) >>
  PURE_ONCE_REWRITE_TAC [type_to_abi_enc_info_def] >>
  irule abi_memory_typed_array_source >> asm_simp_tac bool_ss [] >>
  fs[memory_value_rel_def, type_memory_size_def, EVERY_EL] >>
  rpt strip_tac >> FIRST [first_x_assum drule_all >> simp[] >> NO_TAC, decide_tac]
QED

Theorem abi_typed_memory_dynamic_array:
  !env sfields cenv ty cap.
    abi_memory_env_rel env cenv /\
    abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty) ==>
    abi_typed_memory env (ArrayT ty (Dynamic cap))
      (type_to_abi_enc_info sfields cenv (ArrayT ty (Dynamic cap)))
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_typed_memory_def] >>
  rpt gen_tac >> strip_tac >> drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV array_value` >> Cases_on `array_value` >> gvs[value_has_type_def] >>
  gvs[AllCaseEqs()] >> simp_tac bool_ss [Once vyper_to_abi_type_def] >>
  rename1 `evaluate_type env ty = SOME elem_tv` >>
  rename1 `vyper_to_abi_same env ty vs = SOME avs` >>
  qspecl_then [`env`, `sfields`, `cenv`, `ty`, `elem_tv`, `cap`, `vs`, `avs`, `source`, `span`, `mem`]
    mp_tac abi_memory_typed_dynamic_array >> simp[value_has_type_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI dynamic array: " ^ name)
  end) (DB.thms "abiMemoryTypedArray")
