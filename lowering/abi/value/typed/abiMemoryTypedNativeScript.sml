(* TOP-LEVEL: complete typed source layouts supply the native encoder's
   proved execution contract. Static values and scalar values use actual
   compiler metadata, without assuming a child execution result. *)
Theory abiMemoryTypedNative
Ancestors
  abiMemoryTypedDefs abiMemoryTypedBase abiMemoryTypedMetadata abiNativeEncoding
  compileEnv exprLowering memoryValueDefs valueEncoding vyperABI vyperValue
  vyperTyping contractABI list

Theorem abi_typed_memory_native:
  !env ty info tv v av source span reference.
    abi_typed_memory env ty info /\ evaluate_type env ty = SOME tv /\
    memory_value_rel tv v source reference /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ type_memory_size tv <= span ==>
    abi_native_encoder info source span reference (enc (vyper_to_abi_type env ty) av)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_typed_memory env ty info` (mp_tac o REWRITE_RULE [abi_typed_memory_def]) >>
  disch_then (qspecl_then [`tv`, `v`, `av`, `source`, `span`, `reference`] mp_tac) >>
  impl_tac >- simp[] >> DISCH_TAC >>
  drule (CONJUNCT1 abi_native_encoding) >> simp[]
QED

Theorem abi_native_typed_base:
  !env sfields cenv bt tv v av source span reference.
    abi_memory_env_rel env cenv /\ evaluate_type env (BaseT bt) = SOME tv /\
    memory_value_rel tv v source reference /\ value_has_type tv v /\
    vyper_to_abi env (BaseT bt) v = SOME av /\ type_memory_size tv <= span ==>
    abi_native_encoder (type_to_abi_enc_info sfields cenv (BaseT bt)) source span reference
      (enc (vyper_to_abi_type env (BaseT bt)) av)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_typed_memory env (BaseT bt) (type_to_abi_enc_info sfields cenv (BaseT bt))` by
    (irule abi_typed_memory_base >> simp[]) >>
  qspecl_then [`env`, `BaseT bt`, `type_to_abi_enc_info sfields cenv (BaseT bt)`,
    `tv`, `v`, `av`, `source`, `span`, `reference`] mp_tac abi_typed_memory_native >> simp[]
QED

Theorem abi_native_typed_static:
  !env sfields cenv ty tv v av source span reference.
    abi_memory_env_rel env cenv /\ evaluate_type env ty = SOME tv /\
    ~is_dynamic (vyper_to_abi_type env ty) /\
    memory_value_rel tv v source reference /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ type_memory_size tv <= span ==>
    abi_native_encoder (type_to_abi_enc_info sfields cenv ty) source span reference
      (enc (vyper_to_abi_type env ty) av)
Proof
  rpt gen_tac >> strip_tac >>
  `abi_typed_memory env ty (type_to_abi_enc_info sfields cenv ty)` by
    (irule abi_typed_memory_static >> simp[]) >>
  qspecl_then [`env`, `ty`, `type_to_abi_enc_info sfields cenv ty`,
    `tv`, `v`, `av`, `source`, `span`, `reference`] mp_tac abi_typed_memory_native >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed native ABI encoder: " ^ name)
  end) (DB.thms "abiMemoryTypedNative")
