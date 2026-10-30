Theory abiBuiltinValidWrapped
Ancestors
  abiBuiltinBytesSetup abiBuiltinValidBytes abiValidWrapped abiDecoderBytes
  abiBuiltinDecodeSetup abiBuiltinAllocation abiDecoderContract compileEnv venomState
  contractABI words arithmetic abiBuiltinDecodeCode abiDecoderWrappedBytesFragment
  abiDecoderTypedCompose abiDecoderGuards abiDecoderReentry abiDecoderReentrySequence
  abiDecoderLoop abiEncoderSequence abiEncoder builtinAbi fragExec instIdxIndep valueEncoding
  emitHelperProps exprLoweringProps venomExecSemantics finite_map list rich_list vyperABI
  vyperValue

(* ===== Pre ===== *)

(* Pure wrapped source input and actual builtin preparation for noncanonical bytes. *)

Definition abi_builtin_valid_wrapped_bytes_pre_def:
  abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d s <=>
    (at = Bytes NONE \/ at = String) /\ vyper_decode_valid_enc (Tuple [at]) bs /\
    dec (Tuple [at]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n /\
    abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s
End

Theorem abi_builtin_valid_wrapped_bytes_ready:
  abi_builtin_decode_setup data min_size max_size (abi_decode_bytes_copy_size n) st =
    (ops,ready) /\
  abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d s ==>
  ?prepared. run_inst_seq (emitted_insts st ready) s = OK prepared /\
    abi_valid_wrapped_bytes_pre n at bs payload ready (FST (SND ops)) (FST ops)
      (SND (SND ops)) (p + 32) d prepared /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) (abi_decode_bytes_copy_size n)
      s prepared /\ inst_extends st ready
Proof
  strip_tac >> qpat_x_assum `abi_builtin_valid_wrapped_bytes_pre _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_wrapped_bytes_pre_def]) >>
  drule_all abi_builtin_bytes_setup_resources >> strip_tac >>
  qpat_assum `abi_builtin_valid_bytes_resources _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_valid_bytes_resources_def]) >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [abi_valid_wrapped_bytes_pre_def] >>
  disj2_tac >> qexists_tac `p + 32 + LENGTH bs` >> simp[]
QED

(* ===== Bytes ===== *)

(* Complete noncanonical singleton Bytes/String builtin execution and simulation. *)

Theorem abi_builtin_wrapped_bytes_code:
  lower_abi_decode data (DecComplex T [(DecBytestring n,32,mem_sz)]) min_size max_size outsz
    st = (out,final) ==>
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule abi_decoder_wrapped_bytes_shape >> strip_tac >>
  `inst_extends ready final` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`st`, `ready`, `final`] emitted_insts_append) >>
  impl_tac >- asm_simp_tac bool_ss [GSYM inst_extends_def] >> strip_tac >>
  drule_all inst_extends_trans >> simp[]
QED

Theorem lower_abi_decode_valid_wrapped_bytes_sequence:
  lower_abi_decode data (DecComplex T [(DecBytestring n,32,abi_decode_bytes_copy_size n)])
    min_size max_size (abi_decode_bytes_copy_size n) st = (out,final) /\
  abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand out actual = SOME (n2w d) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    actual.vs_allocas =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_allocas /\
    actual.vs_alloca_next =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_alloca_next /\
    fresh_vars_wrt final actual /\ actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  drule_all abi_builtin_valid_wrapped_bytes_ready >> strip_tac >>
  drule_all abi_valid_wrapped_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready final) prepared = OK actual` >>
  drule abi_decoder_wrapped_bytes_shape >> strip_tac >>
  `inst_extends ready final` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  qpat_assum `abi_valid_wrapped_bytes_pre _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_valid_wrapped_bytes_pre_def]) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  gvs[abi_decode_frame_def, Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >> first_assum ACCEPT_TAC
QED

Theorem lower_abi_decode_valid_wrapped_bytes:
  lower_abi_decode data (DecComplex T [(DecBytestring n,32,abi_decode_bytes_copy_size n)])
    min_size max_size (abi_decode_bytes_copy_size n) st = (out,final) /\ fn_has_code st final func /\
  abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all lower_abi_decode_valid_wrapped_bytes_sequence >> strip_tac >>
  drule abi_builtin_wrapped_bytes_code >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

(* ===== Source ===== *)

(* Complete wrapped builtin result agrees with successful source decoding. *)

Theorem abi_builtin_valid_wrapped_source_pre:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type env ty = SOME tv /\
  evaluate_abi_decode env (TupleT [ty]) bs = INL (ArrayV (TupleV [v])) /\
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s ==>
  ?at payload. abi_builtin_valid_wrapped_bytes_pre n at bs payload st data min_size max_size p d s /\
    (!mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)
Proof
  strip_tac >> gvs[evaluate_type_def, Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  FIRST
  [drule abi_valid_wrapped_bytes_source_decode >> strip_tac >>
     qexistsl_tac [`Bytes NONE`, `payload`] >>
     gvs[abi_builtin_valid_wrapped_bytes_pre_def, Excl "dec_def", Excl "vyper_decode_valid_enc_def"],
   drule abi_valid_wrapped_string_source_decode >> strip_tac >>
     qexistsl_tac [`String`, `payload`] >>
     gvs[abi_builtin_valid_wrapped_bytes_pre_def, Excl "dec_def", Excl "vyper_decode_valid_enc_def"]]
QED

Theorem lower_abi_decode_valid_wrapped_bytes_source:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type env ty = SOME tv /\
  evaluate_abi_decode env (TupleT [ty]) bs = INL (ArrayV (TupleV [v])) /\
  lower_abi_decode data (DecComplex T [(DecBytestring n,32,abi_decode_bytes_copy_size n)])
    min_size max_size (abi_decode_bytes_copy_size n) st = (out,final) /\ fn_has_code st final func /\
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_valid_wrapped_source_pre >> strip_tac >>
  drule_all lower_abi_decode_valid_wrapped_bytes >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED
