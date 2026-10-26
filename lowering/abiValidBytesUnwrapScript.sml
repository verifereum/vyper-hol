(* Both actual unwrap_tuple choices for successful noncanonical Bytes/String.
   TOP-LEVEL: source wrapping inversion and complete translated builtin execution. *)
Theory abiValidBytesUnwrap
Ancestors
  abiBuiltinValidWrapped abiBuiltinValidBytes abiDecoderBytes abiDecoderContract
  abiDecoderReentry abiDecoderLoop abiEncoder builtinAbi fragExec exprLowering compileEnv
  valueEncoding vyperABI vyperContext vyperValue venomState words list

Theorem abi_valid_bytes_lowering:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  needs_external_call_wrap ty /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_to_abi_dec_info sf ce (TupleT [ty]) =
    DecComplex T [(DecBytestring n,32,abi_decode_bytes_copy_size n)] /\
  type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
  type_memory_bytes ce (TupleT [ty]) = abi_decode_bytes_copy_size n
Proof
  strip_tac >> gvs[needs_external_call_wrap_def, type_to_abi_dec_info_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, type_memory_bytes_def,
    abi_decode_bytes_copy_size_def]
QED

Theorem abi_source_decode_wrapping_iff:
  evaluate_type_builtin cx (AbiDecode unwrap) ty [vyperValue$BytesV bs] = INL v <=>
  evaluate_abi_decode (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) bs =
  INL (if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v)
Proof
  Cases_on `unwrap /\ needs_external_call_wrap ty` >>
  gvs[evaluate_type_builtin_def, AllCaseEqs()]
QED

val valid_bytes_source_rules = List.concat (List.map (fn th =>
  [SIMP_RULE bool_ss [] (Q.INST [`ty` |-> `BaseT (BytesT (Dynamic n))`] th),
   SIMP_RULE bool_ss [] (Q.INST [`ty` |-> `BaseT (StringT n)`] th)])
  [lower_abi_decode_valid_wrapped_bytes_source, lower_abi_decode_valid_bytes_source]);

Theorem lower_abi_decode_valid_bytes_unwrap:
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty [vyperValue$BytesV bs] = INL v /\
  lower_abi_decode data (type_to_abi_dec_info sf ce wrapped_ty) min_size max_size
    (type_memory_bytes ce wrapped_ty) st = (out,final) /\ fn_has_code st final func /\
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ty) initial actual /\ fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_bytes_lowering >> strip_tac >>
  qpat_x_assum `evaluate_type_builtin _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_source_decode_wrapping_iff]) >>
  Cases_on `unwrap` >> gvs[needs_external_call_wrap_def, Excl "dec_def", Excl "valid_enc_def"] >>
  FIRST (List.map (fn th => drule_all th >>
    disch_then (qspec_then `ctx` strip_assume_tac)) valid_bytes_source_rules) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
