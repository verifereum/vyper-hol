Theory abiBuiltinEncodeSource
Ancestors
  vyperContext vyperABI vyperTypeSystem vyperAST contractABI list arithmetic abiBuiltinEncodeRun
  abiBuiltinEncodeMethod builtinAbi valueEncodingProofs cv_std byte words rich_list divides
  abiBuiltinEncodeInput abiBuiltinEncodeEffect abiDecoderContract abiDecoderLoop fragExec
  exprLowering compileEnv valueEncoding venomState venomExecSemantics

(* ===== Model ===== *)

(* The source builtin selects the same singleton or tuple payload as lowering. *)

Definition abi_builtin_encode_type_def:
  abi_builtin_encode_type ensure tys =
    if LENGTH tys = 1 /\ ~ensure then HD tys else TupleT tys
End

Definition abi_builtin_encode_value_def:
  abi_builtin_encode_value ensure tys vs =
    if LENGTH tys = 1 /\ ~ensure then HD vs else ArrayV (TupleV vs)
End

Theorem abi_builtin_encode_source_single:
  vyper_to_abi (get_tenv cx) ty v = SOME av ==>
  evaluate_type_builtin cx (AbiEncode F method_id) (TupleT [ty]) arg_tys [v] =
    INL (BytesV (abi_encode_method_id_bytes method_id ++ enc (vyper_to_abi_type (get_tenv cx) ty) av))
Proof
  simp[evaluate_type_builtin_def, evaluate_abi_encode_bytes_def, needs_external_call_wrap_def, LET_THM]
QED

Theorem abi_builtin_encode_source_tuple:
  ~(~ensure /\ LENGTH tys <= 1) /\ vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) = SOME av ==>
  evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs =
    INL (BytesV (abi_encode_method_id_bytes method_id ++
      enc (vyper_to_abi_type (get_tenv cx) (TupleT tys)) av))
Proof
  strip_tac >>
  asm_simp_tac (srw_ss()) [evaluate_type_builtin_def, evaluate_abi_encode_bytes_def,
    needs_external_call_wrap_def, LET_THM]
QED

Theorem abi_builtin_encode_source_result:
  tys <> [] /\ LENGTH vs = LENGTH tys /\
  vyper_to_abi (get_tenv cx) (abi_builtin_encode_type ensure tys)
    (abi_builtin_encode_value ensure tys vs) = SOME av ==>
  evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs =
    INL (BytesV (abi_encode_method_id_bytes method_id ++
      enc (vyper_to_abi_type (get_tenv cx) (abi_builtin_encode_type ensure tys)) av))
Proof
  Cases_on `ensure` >>
  simp_tac (srw_ss()) [abi_builtin_encode_type_def, abi_builtin_encode_value_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac (srw_ss()) [evaluate_type_builtin_def, evaluate_abi_encode_bytes_def,
    needs_external_call_wrap_def, LET_THM] >>
  Cases_on `tys` >> gvs[] >> rename1 `LENGTH vs = SUC (LENGTH tail_tys)` >>
  Cases_on `tail_tys` >> gvs[LENGTH_EQ_NUM_compute]
QED

(* ===== Prefix ===== *)

(* Connect the dispatcher's byte-list method ID to the actual shifted word
   store and the source evaluator's prefix. *)

Theorem abi_builtin_method_word_aligned:
  LENGTH bs = 4 ==>
  bytes_method_id_word bs << 224 = (word_of_bytes_be bs:bytes32)
Proof
  strip_tac >>
  `(word_of_bytes_be bs:bytes32) = n2w (num_of_bytes (be_bytes 32 [] bs))` by
    (irule (SIMP_RULE (srw_ss()) [divides_def]
      (INST_TYPE [alpha |-> ``:256``] word_of_bytes_be_eq_num_of_bytes)) >>
     qexists_tac `32` >> simp[]) >>
  `TAKE 32 (bs ++ REPLICATE 32 0w) = bs ++ REPLICATE 28 0w` by
    simp[TAKE_APPEND, TAKE_LENGTH_TOO_LONG, REPLICATE_GENLIST, TAKE_GENLIST] >>
  asm_simp_tac (srw_ss()) [bytes_method_id_word_def, be_bytes_thm, REVERSE_APPEND,
    REVERSE_REPLICATE, num_of_bytes_APPEND, word_lsl_n2w, MULT_COMM]
QED

Theorem abi_builtin_method_word_prefix:
  LENGTH bs = 4 ==>
  abi_builtin_encode_method_bytes (bytes_method_id_word bs) = bs
Proof
  strip_tac >> drule abi_builtin_method_word_aligned >> strip_tac >>
  mp_tac (Q.SPEC `bs` TAKE_word_to_bytes_be_word_of_bytes_be) >>
  asm_simp_tac (srw_ss()) [abi_builtin_encode_method_bytes_def, word_to_bytes_be_def]
QED

Theorem abi_builtin_encode_source_prefix:
  (case method_id of NONE => T | SOME bs => LENGTH bs = 4) ==>
  abi_builtin_encode_prefix (OPTION_MAP bytes_method_id_word method_id) =
    abi_encode_method_id_bytes method_id
Proof
  Cases_on `method_id` >> simp[abi_builtin_encode_prefix_def, abi_encode_method_id_bytes_def] >>
  strip_tac >> drule abi_builtin_method_word_prefix >> simp[]
QED

Theorem abi_builtin_encode_checked_prefix:
  well_typed_type_builtin_args (AbiEncode ensure method_id) target_ty arg_tys ==>
  abi_builtin_encode_prefix (OPTION_MAP bytes_method_id_word method_id) =
    abi_encode_method_id_bytes method_id
Proof
  simp_tac bool_ss [well_typed_type_builtin_args_def] >> strip_tac >>
  irule abi_builtin_encode_source_prefix >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_encode_store_case:
  (case OPTION_MAP bytes_method_id_word method_id of NONE => 0 | SOME _ => 32) =
  (case method_id of NONE => 0 | SOME _ => 32)
Proof
  Cases_on `method_id` >> simp[]
QED

(* ===== Correct ===== *)

(* Source-value correctness of the complete lower_abi_encode action, for both
   singleton unwrapping and tuple payloads and either optional method ID. *)

Theorem lower_abi_encode_source:
  let enc_ty = abi_builtin_encode_type ensure tys in
  let bytes = abi_encode_method_id_bytes method_id ++ enc (vyper_to_abi_type (get_tenv cx) enc_ty) av in
  well_typed_type_builtin_args (AbiEncode ensure method_id) (TupleT tys) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_to_abi (get_tenv cx) enc_ty (abi_builtin_encode_value ensure tys vs) = SOME av /\
  lower_abi_encode ensure (OPTION_MAP bytes_method_id_word method_id) src
    (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_pre (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty)
    (vyper_to_abi_type (get_tenv cx) enc_ty) av start (OPTION_MAP bytes_method_id_word method_id)
    src sb source_cap p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs = INL (BytesV bytes) /\
    eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH bytes) /\
    mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    FLOOKUP actual.vs_allocas start.cs_next_id =
      SOME (p,maxlen+32+LENGTH (abi_encode_method_id_bytes method_id)) /\
    abi_builtin_encode_effect first last start final limit_st p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_checked_prefix >> strip_tac >>
  qpat_assum `well_typed_type_builtin_args _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [well_typed_type_builtin_args_def]) >>
  drule_all abi_builtin_encode_source_result >> disch_then (qspec_then `method_id` assume_tac) >>
  drule_all lower_abi_encode_run >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_builtin_encode_prefix _ = _` (fn prefix =>
    RULE_ASSUM_TAC (PURE_REWRITE_RULE [prefix, abi_builtin_encode_store_case])) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
