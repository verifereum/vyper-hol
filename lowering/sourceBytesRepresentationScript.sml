(* Forward source conversion for allocation-free bytes/string leaves. *)
Theory sourceBytesRepresentation
Ancestors abiDecoderBytestring abiDecoderString abiDecoderCoherence
  vyperABI vyperTyping vyperValue compileEnv valueEncoding exprLowering
  contractABI list abiDecoderBytes calldataTypedRobustPtr abiDecoderBytestringCases

Theorem coherent_source_bytes_representation:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
  ?bs. av = contractABI$BytesV bs /\ LENGTH bs <= n /\
    enc (vyper_to_abi_type env ty) av =
      enc (contractABI$Bytes NONE) (contractABI$BytesV bs) /\
    type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
    (!d mem. val_in_memory tv v d mem <=>
      val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d mem)
Proof
  strip_tac >> drule abi_decoder_bytestring_cases >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def, vyper_to_abi_base_def] >>
  simp[type_memory_bytes_def, abi_decode_bytes_copy_size_def,
       val_in_memory_def, enc_def, vyperMiscTheory.n2w_o_ORD_eq]
QED

Theorem calldata_source_bytes_ptr_endpoint_uniform:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring m /\
  evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring m) sa = ((),sb) /\
  C = 32 + 32 * ((m + 31) DIV 32) /\ C < dimword (:256) /\
  m < dimword (:256) /\
  eval_operand (Var p) s = SOME dw /\
  eval_operand src s = SOME (n2w srcpos) /\ srcpos < dimword (:256) /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    s.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  fresh_vars_wrt sa s /\ ptr_covers G tn p s C /\
  op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s' G' tn'.
    run_inst_seq (emitted_insts sa sb) s =
      OK (s' with vs_inst_idx := s.vs_inst_idx) /\
    ~s'.vs_halted /\ s'.vs_current_bb = sb.cs_current_bb /\
    s'.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand (Var p) s' = SOME dw /\
    eval_operand src s' = SOME (n2w srcpos) /\
    s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next /\
    ptr_covers G' tn' p s' C /\
    (!i. w2n dw <= i /\ i < w2n dw + C ==> i NOTIN tn'.t_mem) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem SUBSET tn.t_mem /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG G' tn' s') ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) /\
    (!mem. mem_agree_outside tn'.t_mem s'.vs_memory mem ==>
      val_in_memory tv v (w2n dw) mem)
Proof
  strip_tac >> drule_all coherent_source_bytes_representation >> strip_tac >>
  qpat_x_assum `av = _` SUBST_ALL_TAC >>
  qpat_assum `!d mem. val_in_memory tv v d mem <=> _`
    (fn th => pure_rewrite_tac [th]) >>
  irule calldata_canonical_bytestring_typed_robust_uniform >> simp[] >> gvs[]
QED
