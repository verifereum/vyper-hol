Theory stmtSimLogDataInput
Ancestors
  stmtSimLogDataRun stmtSimLogSource abiEncoderSourceCorrect
  abiBuiltinEncodeWord entryDecodeProps entryDecodeStaticProps
  supportedTypes vyperTyping vyperABI contractABI vyperValue words integer arithmetic typedCopyMetadata
  abiEncoderInput valueEncoding compileEnv exprLowering stmtSimLogData
  valueEncodingProps list abiDecodeRanges exprSimAttributeFields vyperTypeDefaults abiDecoderMembers

Theorem log_word_abi_type:
  supported_word_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
  has_type (vyper_to_abi_type env ty) av /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  static_length (vyper_to_abi_type env ty) = 32
Proof
  cheat
QED

Theorem log_word_memory_input:
  supported_word_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v p mem ==>
  ?av. vyper_to_abi env ty v = SOME av /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty)
      (vyper_to_abi_type env ty) av p (type_memory_bytes ce ty) mem
Proof
  cheat
QED

Theorem log_scalar_memory_input:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v p mem /\
  type_memory_bytes ce ty < dimword (:256) ==>
  ?av. vyper_to_abi env ty v = SOME av /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty)
      (vyper_to_abi_type env ty) av p (type_memory_bytes ce ty) mem
Proof
  cheat
QED

Theorem log_scalar_abi_metadata:
  supported_scalar_type ty ==>
  is_abi_dynamic sf ty = is_dynamic (vyper_to_abi_type env ty) /\
  abi_embedded_static_size sf ty = abi_member_head_size (vyper_to_abi_type env ty) /\
  (~is_dynamic (vyper_to_abi_type env ty) ==>
    static_length (vyper_to_abi_type env ty) = type_memory_bytes ce ty)
Proof
  cheat
QED

Theorem log_data_layout_inputs:
  !tys vs p.
    EVERY supported_scalar_type tys /\
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                          value_has_type tv v) tys vs /\
    log_data_layout cx tys vs p mem /\
    SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
    ?avs. vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
      LIST_REL (\ty av. has_type (vyper_to_abi_type (get_tenv cx) ty) av) tys avs /\
      (!i. i < LENGTH tys ==>
        abi_encoder_input (type_to_abi_enc_info sf ce (EL i tys))
          (vyper_to_abi_type (get_tenv cx) (EL i tys)) (EL i avs)
          (p + SUM (MAP (type_memory_bytes ce) (TAKE i tys)))
          (type_memory_bytes ce (EL i tys)) mem)
Proof
  cheat
QED

Theorem log_tuple_abi_metadata[local]:
  !tys. EVERY supported_scalar_type tys ==>
  is_abi_dynamic sf (TupleT tys) =
    is_dynamic (vyper_to_abi_type env (TupleT tys)) /\
  type_memory_bytes ce (TupleT tys) = SUM (MAP (type_memory_bytes ce) tys) /\
  (~is_dynamic (vyper_to_abi_type env (TupleT tys)) ==>
    static_length (vyper_to_abi_type env (TupleT tys)) =
      SUM (MAP (type_memory_bytes ce) tys))
Proof
  cheat
QED

Theorem log_tuple_types[local]:
  !tys tvs vs.
    EVERY supported_scalar_type tys /\
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    LIST_REL (\ty v. ?tv. evaluate_type env ty = SOME tv /\ value_has_type tv v) tys vs ==>
    LIST_REL value_has_type tvs vs /\
    type_memory_size_list tvs = SUM (MAP (type_memory_bytes ce) tys) /\
    !acc. evaluate_types env tys acc = SOME (REVERSE acc ++ tvs)
Proof
  cheat
QED

Theorem log_data_layout_typed_tuple:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  log_data_layout cx tys vs p mem /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
  ?tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
    value_has_type tv (ArrayV (TupleV vs)) /\
    val_in_memory tv (ArrayV (TupleV vs)) p mem /\
    type_memory_size tv = SUM (MAP (type_memory_bytes ce) tys)
Proof
  cheat
QED

Theorem log_scalar_memory_positive[local]:
  supported_scalar_type ty ==> 0 < type_memory_bytes ce ty
Proof
  cheat
QED

Theorem log_tuple_length_bound[local]:
  !tys. EVERY supported_scalar_type tys ==>
    LENGTH tys <= SUM (MAP (type_memory_bytes ce) tys)
Proof
  cheat
QED

Theorem log_data_layout_input:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  log_data_layout cx tys vs p mem /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword (:256) ==>
  ?avs. vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    abi_encoder_input (type_to_abi_enc_info sf ce (TupleT tys))
      (vyper_to_abi_type (get_tenv cx) (TupleT tys)) (ListV avs) p
      (SUM (MAP (type_memory_bytes ce) tys)) mem
Proof
  cheat
QED

Theorem log_data_sources_typed:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs ==>
    LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                          value_has_type tv v) (MAP SND xs) vs
Proof
  cheat
QED

Theorem compile_log_store_data_input:
  compile_log_store_data cenv xs buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) ==>
  inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?t avs. run_inst_seq (emitted_insts sa sb) s = OK t /\
    log_data_layout cx (MAP SND xs) vs (b + off) t.vs_memory /\
    log_write_frame sa (b + off)
      (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) s t /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op ty. MEM (op,ty) xs ==> eval_operand op t = eval_operand op s) /\
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    abi_encoder_input (type_to_abi_enc_info sf cenv (TupleT (MAP SND xs)))
      (vyper_to_abi_type (get_tenv cx) (TupleT (MAP SND xs))) (ListV avs)
      (b + off) (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) t.vs_memory
Proof
  cheat
QED
