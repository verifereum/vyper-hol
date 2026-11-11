(* Source outcomes stay separate from physical execution resources. *)
Theory abiDecodePtrSourceOutcome
Ancestors
  abiDecodePtrPhysicalFlatRun abiValidMembers abiValidBytesUnwrap abiDecoderCoherence
  exprSimAbiDecodeReject exprSimAbiDecodeGas
  vyperABI vyperContext vyperTypeABI valueEncoding words list

(* In particular, conversion failure is not the invalid-input exemption. *)
Theorem abi_decode_source_error_iff:
  evaluate_abi_decode env ty bs = INR err <=>
    (~vyper_valid_enc env ty bs /\ err = "abi_decode invalid") \/
    (vyper_valid_enc env ty bs /\
     abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = NONE /\
     err = "abi_decode conversion")
Proof
  Cases_on `vyper_valid_enc env ty bs` >>
  simp[evaluate_abi_decode_def, decode_abi_value_def, AllCaseEqs()] >>
  metis_tac[]
QED

(* Apply the physical runner to actual source bytes, without re-encoding. *)
Theorem abi_decode_physical_source_run:
  EVERY supported_scalar_type tys /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields (TupleT tys) (TupleTV tvs) /\
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys [BytesV bs] =
    INL (ArrayV (TupleV vs)) /\
  compile_abi_decode_to_buf (Var dst) pos MLOAD (Var src) hi
    (DecComplex dyn (abi_decoder_member_infos ce.ce_struct_fields ce tys)) st = ((),last) /\
  mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD s) = bs /\
  B+z+LENGTH bs < dimword(:256) /\
  d+SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) /\
  (B+z+LENGTH bs <= d \/ d+SUM (MAP (type_memory_bytes ce) tys) <= B+z) /\
  eval_operand (Var src) s = SOME (n2w B) /\
  eval_operand pos s = SOME (n2w z) /\ eval_operand (Var dst) s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var pos /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  abi_decoder_operand_live st.cs_next_var (Var src) /\
  abi_decoder_operand_live st.cs_next_var hi /\ fresh_vars_wrt st s /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
    z+LENGTH bs <= h /\ h < dimword(:256)) ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\ inst_extends st last /\
    tuple_in_memory vs tvs d t.vs_memory /\
    abi_decode_frame d (SUM (MAP (type_memory_bytes ce) tys)) s t /\
    fresh_vars_wrt last t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    mem_bytes_at (B+z) (LENGTH bs) (abi_decode_source MLOAD t) = bs /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `evaluate_type_builtin _ _ _ _ _ = _`
    (assume_tac o REWRITE_RULE [abi_source_decode_wrapping_iff]) >>
  drule abi_valid_tuple_source_values >> strip_tac >>
  irule abi_decode_physical_flat_run >>
  gvs[abi_decoder_coherent_tuple_iff] >> metis_tac[]
QED
