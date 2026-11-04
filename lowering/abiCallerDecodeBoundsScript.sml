Theory abiCallerDecodeBounds
Ancestors
  abiCallerBuiltinInput compileVyper compileEnv vyperTypeSystem vyperValue vyperTyping
  vyperContext list abiCallerAbiBound abiValidBytesUnwrap vyperABI context

(* Singleton wrapping preserves source type evaluation and actual caller
   coherence, with no extra slot-size assumption. *)
Theorem abi_caller_singleton_type:
  evaluate_type env ty = SOME tv ==>
  evaluate_type env (TupleT [ty]) = SOME (TupleTV [tv])
Proof
  strip_tac >> drule (cj 1 evaluate_type_well_formed) >> strip_tac >>
  drule well_formed_type_value_slot_size >>
  simp[evaluate_type_def, type_slot_size_def]
QED

Theorem abi_caller_wrapped_coherent:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv ==>
  abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type
      code_stmts use_trans).ce_struct_fields
    (if wrapped then TupleT [ty] else ty) (if wrapped then TupleTV [tv] else tv)
Proof
  strip_tac >> drule abi_caller_singleton_type >> strip_tac >>
  `assignable_type (type_env tops) (TupleT [ty])` by
    simp[Once assignable_type_def, well_formed_type_def] >>
  Cases_on `wrapped` >> irule abi_caller_coherent >> simp[] >>
  qexists_tac `in_deploy` >> simp[]
QED

(* Both emitted builtin length guards follow from successful source decoding
   under the actual checked compiler-environment construction. *)
Theorem abi_caller_source_decode_bounds:
  let sf = (build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans).ce_struct_fields in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v ==>
  abi_static_size sf ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf ty
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >> conj_tac
  >- (mp_tac abi_caller_source_decode_minimum >> asm_simp_tac bool_ss []) >>
  mp_tac abi_caller_source_decode_maximum >> asm_simp_tac bool_ss []
QED

Theorem abi_caller_source_decode_wrapped_bounds:
  let sf = (build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans).ce_struct_fields in
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  get_tenv cx = type_env tops /\
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [BytesV bs] = INL v ==>
  abi_static_size sf wrapped_ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf wrapped_ty
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `evaluate_type_builtin _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_source_decode_wrapping_iff]) >>
  qpat_assum `get_tenv cx = type_env tops`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `evaluate_type (type_env tops)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) =
    SOME (if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv)` by
    (Cases_on `unwrap /\ needs_external_call_wrap ty` >> simp[abi_caller_singleton_type]) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] (Q.INST
    [`ty` |-> `if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty`,
     `tv` |-> `if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv`,
     `v` |-> `if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v`]
    abi_caller_source_decode_bounds)) >>
  asm_simp_tac bool_ss []
QED
