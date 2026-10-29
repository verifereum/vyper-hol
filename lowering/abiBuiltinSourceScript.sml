Theory abiBuiltinSource
Ancestors
  abiBuiltinCanonicalPre abiBuiltinAllocation abiBuiltinDecodeSetup abiDecoderCoherence
  abiDecoderTypedContract abiDecoderAllocation abiDecoderFrame valueEncoding valueEncodingProps
  vyperABI vyperTypeABI contractABI compileEnv venomState finite_map words list arithmetic
  abiBuiltinUnwrapCorrect abiBuiltinDecodeEffect abiDecoderContract abiDecoderLoop builtinAbi
  fragExec vyperContext venomExecSemantics

(* ===== Input ===== *)

(* Establish builtin inputs from the source Bytes value and its decode result.
   Canonicality and numeric allocator bounds remain explicit caller obligations. *)

Definition abi_builtin_decode_resources_def:
  abi_builtin_decode_resources st first last min_size max_size outsz cnt p d b cap s <=>
    min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
    p + 32 + cnt < dimword (:256) /\ d + outsz < dimword (:256) /\
    (d + outsz <= b \/ b + cap <= d) /\
    abi_footprint_disjoint (p + 32) cnt [(d,outsz);(b,cap)] /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,outsz)) /\
    first <= abi_builtin_decode_output_site st min_size max_size + 2 /\
    abi_decoder_budget first last b cap
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size) outsz s)
End

Theorem abi_builtin_source_metadata:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_abi_decode env ty bs = INL v ==>
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec (vyper_to_abi_type env ty) bs) v
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  qpat_x_assum `evaluate_abi_decode _ _ _ = _` mp_tac >>
  simp[evaluate_abi_decode_def, decode_abi_value_def, AllCaseEqs()] >> strip_tac >>
  `has_type (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)` by
    (irule (cj 1 dec_has_type) >> fs[vyper_valid_enc_def]) >>
  `value_has_type tv v` by
    (irule (cj 1 abi_to_vyper_well_typed) >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`dec (vyper_to_abi_type env ty) bs`, `env`, `ty`] >>
     asm_simp_tac bool_ss []) >>
  irule abi_decoder_coherent_root_metadata >> asm_simp_tac bool_ss [] >>
  qexists_tac `sf` >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_canonical_pre_from_source:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_abi_decode env ty bs = INL v /\
  bs = enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_canonical_pre ce env sf ty tv (dec (vyper_to_abi_type env ty) bs) v st
    first last data min_size max_size p d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_source_metadata >> strip_tac >>
  qpat_x_assum `bs = enc _ _` (assume_tac o SYM) >>
  gvs[abi_builtin_canonical_pre_def, abi_builtin_decode_resources_def,
     val_in_memory_def, mem_word_at_eq_mload, Excl "enc_def"]
QED

(* ===== Correct ===== *)

(* Whole builtin execution from a source Bytes value already in memory. *)

Theorem lower_abi_decode_source_canonical:
  let wrapped = (unwrap /\ needs_external_call_wrap ty) in
  let wrapped_ty = if wrapped then TupleT [ty] else ty in
  let wrapped_tv = if wrapped then TupleTV [tv] else tv in
  let wrapped_v = if wrapped then ArrayV (TupleV [v]) else v in
  lower_abi_decode data (type_to_abi_dec_info sf ce wrapped_ty) min_size max_size
    (type_memory_bytes ce wrapped_ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce (get_tenv cx) sf wrapped_ty wrapped_tv /\
  evaluate_abi_decode (get_tenv cx) wrapped_ty bs = INL wrapped_v /\
  bs = enc (vyper_to_abi_type (get_tenv cx) wrapped_ty)
    (dec (vyper_to_abi_type (get_tenv cx) wrapped_ty) bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\
  abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce wrapped_ty)
    (LENGTH bs) src_base d b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [BytesV bs] = INL v /\
    eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_canonical_pre_from_source >> strip_tac >>
  mp_tac (Q.INST [`av` |->
    `dec (vyper_to_abi_type (get_tenv cx)
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) bs`]
    lower_abi_decode_unwrap_canonical) >>
  asm_simp_tac bool_ss [LET_THM]
QED

Theorem lower_abi_decode_source_unwrap_true_canonical =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `T`] lower_abi_decode_source_canonical);
