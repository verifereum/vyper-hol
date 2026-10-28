(* TOP-LEVEL: the compiler's actual metadata satisfies the typed memory
   contract for all scalar types, None, and arbitrary static aggregates. *)
Theory abiMemoryTypedBase
Ancestors
  abiMemoryTypedDefs abiMemoryTypedLeaf abiMemoryTypedMetadata abiMemoryEncoding
  abiTypeShape memoryValueAbiStatic memoryValueAbiTuple valueLoadProps exprLowering compileEnv
  valueEncoding vyperABI vyperTyping vyperValue vyperTypeValues
  contractABI list words

Theorem abi_typed_memory_none:
  !env. abi_typed_memory env NoneT (AbiComplex [])
Proof
  simp_tac bool_ss [abi_typed_memory_def] >> rpt gen_tac >>
  simp[evaluate_type_def] >> strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_type_def, Once enc_def,
    abiFieldLayoutDefsTheory.abi_field_bytes_def,
    abiFieldLayoutDefsTheory.abi_field_head_size_def,
    abiFieldLayoutDefsTheory.abi_field_heads_def,
    abiFieldLayoutDefsTheory.abi_field_tails_def] >>
  qspecl_then [`[]`, `source`, `span`, `mem`, `[]`] mp_tac abi_memory_encoding_complex >>
  simp[abiFieldLayoutDefsTheory.abi_field_bytes_def,
    abiFieldLayoutDefsTheory.abi_field_head_size_def,
    abiFieldLayoutDefsTheory.abi_field_heads_def,
    abiFieldLayoutDefsTheory.abi_field_tails_def, abi_memory_encoding_fields_nil,
    listTheory.REV_REVERSE_LEM]
QED

Theorem abi_typed_memory_static:
  !env sfields cenv ty.
    abi_memory_env_rel env cenv /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
    abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ty = NoneT`
  >- gvs[type_to_abi_enc_info_def, abi_typed_memory_none] >>
  PURE_REWRITE_TAC [abi_typed_memory_def] >> rpt gen_tac >> strip_tac >>
  `abi_struct_env_rel env cenv.ce_struct_fields /\
   type_memory_bytes cenv ty = type_memory_size tv` by
    (fs[abi_memory_env_rel_def] >> first_x_assum drule_all >> simp[]) >>
  drule_all evaluated_static_encoder_info >> DISCH_TAC >> simp[] >>
  qspecl_then [`env`, `ty`, `tv`, `v`, `av`, `source`, `span`, `mem`]
    mp_tac abi_memory_typed_copy >> simp[]
QED

Theorem abi_typed_memory_bytes:
  !env cap. abi_typed_memory env (BaseT (BytesT (Dynamic cap))) (AbiBytestring cap)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [abi_typed_memory_def] >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_base_identity >> DISCH_TAC >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def, vyper_to_abi_type_def] >>
  rename1 `memory_value_rel _ (vyperValue$BytesV bs) source mem` >>
  qspecl_then [`env`, `cap`, `bs`, `source`, `span`, `mem`]
    mp_tac abi_memory_typed_bytes >> simp[value_has_type_def]
QED

Theorem abi_typed_memory_string:
  !env cap. abi_typed_memory env (BaseT (StringT cap)) (AbiBytestring cap)
Proof
  rpt gen_tac >> PURE_REWRITE_TAC [abi_typed_memory_def] >> rpt gen_tac >> strip_tac >>
  drule evaluate_type_base_identity >> DISCH_TAC >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def, vyper_to_abi_type_def] >>
  rename1 `memory_value_rel _ (StringV s) source mem` >>
  qspecl_then [`env`, `cap`, `s`, `source`, `span`, `mem`]
    mp_tac abi_memory_typed_string >> simp[value_has_type_def, vyperMiscTheory.n2w_o_ORD_eq]
QED

Theorem abi_typed_memory_base:
  !env sfields cenv bt.
    abi_memory_env_rel env cenv ==>
    abi_typed_memory env (BaseT bt) (type_to_abi_enc_info sfields cenv (BaseT bt))
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `bt` >>
  FIRST [irule abi_typed_memory_static >> simp[vyper_to_abi_type_def] >> NO_TAC,
    simp[type_to_abi_enc_info_def, abi_typed_memory_string] >> NO_TAC,
    rename1 `BytesT byte_bound` >> Cases_on `byte_bound` >>
    FIRST [irule abi_typed_memory_static >> simp[vyper_to_abi_type_def] >> NO_TAC,
      simp[type_to_abi_enc_info_def, abi_typed_memory_bytes]]]
QED

Theorem abi_typed_memory_flag:
  !env sfields cenv nsid.
    abi_memory_env_rel env cenv ==>
    abi_typed_memory env (FlagT nsid) (type_to_abi_enc_info sfields cenv (FlagT nsid))
Proof
  rpt strip_tac >> irule abi_typed_memory_static >> simp[vyper_to_abi_type_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI memory base: " ^ name)
  end) (DB.thms "abiMemoryTypedBase")
