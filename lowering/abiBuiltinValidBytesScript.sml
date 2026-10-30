Theory abiBuiltinValidBytes
Ancestors
  abiDecoderValidBytes abiDecoderBytes abiBuiltinDecodeSetup abiBuiltinSetupExecute
  abiBuiltinAllocation abiDecoderReentry abiDecoderContract valueEncoding valueEncodingProps
  emitHelperProps compileEnv venomState contractABI finite_map words list arithmetic
  abiBuiltinDecodeCode abiDecoderBytesTyped abiDecoderGuards abiDecoderReentrySequence
  abiDecoderTypedCompose abiEncoder builtinAbi exprLoweringProps venomExecSemantics rich_list
  abiDecoderLoop abiEncoderSequence fragExec instIdxIndep abiValidBytesSource vyperABI
  vyperValue

(* ===== Pre ===== *)

(* Incoming resources for the complete builtin Bytes/String decoder.
   The source is its actual Bytes value, without a canonical encoding premise. *)

Definition abi_builtin_valid_bytes_resources_def:
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s <=>
    val_in_memory (BaseTV (BytesT (Dynamic (LENGTH bs)))) (vyperValue$BytesV bs) p s.vs_memory /\
    eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
    min_size <= LENGTH bs /\ LENGTH bs <= max_size /\ max_size < dimword (:256) /\
    n < dimword (:256) /\ p + 32 + LENGTH bs < dimword (:256) /\
    d + abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt st s /\
    ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
        d = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
        SOME (d,abi_decode_bytes_copy_size n))
End

Definition abi_builtin_valid_bytes_pre_def:
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d s <=>
    (at = Bytes NONE \/ at = String) /\ vyper_decode_valid_enc at bs /\
    dec at bs = contractABI$BytesV payload /\ LENGTH payload <= n /\
    abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s
End

Theorem abi_builtin_valid_bytes_ready:
  abi_builtin_decode_setup data min_size max_size (abi_decode_bytes_copy_size n) st =
    (ops,ready) /\
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d s ==>
  ?prepared. run_inst_seq (emitted_insts st ready) s = OK prepared /\
    abi_decoder_valid_bytes_pre n at bs payload ready (FST (SND ops)) (FST ops)
      MLOAD (SND (SND ops)) (p + 32) d prepared /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) (abi_decode_bytes_copy_size n)
      s prepared /\ inst_extends st ready
Proof
  strip_tac >> qpat_x_assum `abi_builtin_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE
      [abi_builtin_valid_bytes_pre_def, abi_builtin_valid_bytes_resources_def]) >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ p < dimword (:256) /\
   abi_decode_bytes_copy_size n < dimword (:256)` by decide_tac >>
  `fresh_vars_wrt ready s` by
    (irule fresh_vars_wrt_mono >> qexists_tac `st` >> simp[GREATER_EQ]) >>
  `mload (w2n (n2w p:bytes32)) s = n2w (LENGTH bs)` by
    fs[val_in_memory_def, mem_word_at_eq_mload, w2n_n2w] >>
  drule_all (SIMP_RULE bool_ss [LESS_EQ_REFL]
    (Q.INST [`limit_st` |-> `ready`] abi_builtin_decode_setup_execute)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK prepared` >>
  qexists_tac `prepared` >> asm_simp_tac bool_ss [] >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac (srw_ss()) [abi_decoder_valid_bytes_pre_def, abi_decode_source_def,
    abi_decode_source_opcode_def, word_add_n2w] >> conj_tac
  >- fs[val_in_memory_def] >>
  disj2_tac >> qexists_tac `p + 32 + LENGTH bs` >> simp[]
QED

(* ===== Builtin Valid Bytes ===== *)

(* Complete lower_abi_decode Bytes/String execution for all valid input windows.
   Actual setup, allocation and decoder execution are composed here. *)

Theorem abi_builtin_bytes_code:
  lower_abi_decode data (DecBytestring n) min_size max_size outsz st = (out,final) ==>
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb /\
  inst_extends st final /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st final)
Proof
  strip_tac >> drule lower_abi_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends ready final` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`st`, `ready`, `final`] emitted_insts_append) >>
  impl_tac >- asm_simp_tac bool_ss [GSYM inst_extends_def] >> strip_tac >>
  drule_all inst_extends_trans >> simp[]
QED

Theorem lower_abi_decode_valid_bytes_sequence:
  lower_abi_decode data (DecBytestring n) min_size max_size
    (abi_decode_bytes_copy_size n) st = (out,final) /\
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d initial ==>
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
  drule_all abi_builtin_valid_bytes_ready >> strip_tac >>
  drule_all abi_decoder_valid_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts ready final) prepared = OK actual` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends ready final` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decoder_sequence_halted >> strip_tac >>
  qpat_assum `abi_decoder_valid_bytes_pre _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_bytes_pre_def]) >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  gvs[abi_decode_frame_def, Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >> first_assum ACCEPT_TAC
QED

(* ===== Reach ===== *)

(* Containing-function execution of the complete noncanonical bytes decoder. *)

Theorem lower_abi_decode_valid_bytes:
  lower_abi_decode data (DecBytestring n) min_size max_size
    (abi_decode_bytes_copy_size n) st = (out,final) /\ fn_has_code st final func /\
  abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w d) /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d actual.vs_memory /\
    val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d actual.vs_memory /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) initial actual /\
    actual.vs_allocas =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_allocas /\
    actual.vs_alloca_next =
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size)
        (abi_decode_bytes_copy_size n) initial).vs_alloca_next /\
    fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all lower_abi_decode_valid_bytes_sequence >> strip_tac >>
  drule abi_builtin_bytes_code >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  gvs[fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >>
  first_assum ACCEPT_TAC
QED

(* ===== Source ===== *)

(* Source-evaluator correctness of complete noncanonical Bytes/String decoding.
   Remaining resource premises concern the actual buffer, allocation and guards. *)

Theorem abi_builtin_valid_bytes_source_pre:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type env ty = SOME tv /\ evaluate_abi_decode env ty bs = INL v /\
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s ==>
  ?at payload. abi_builtin_valid_bytes_pre n at bs payload st data min_size max_size p d s /\
    (!mem. val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV payload) d mem /\
      val_in_memory (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) payload)) d mem ==>
      val_in_memory tv v d mem)
Proof
  strip_tac >> gvs[evaluate_type_def, Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  FIRST
  [drule abi_valid_bytes_source_decode >> strip_tac >>
     qexistsl_tac [`Bytes NONE`, `payload`] >>
     gvs[abi_builtin_valid_bytes_pre_def, abi_builtin_valid_bytes_resources_def,
       Excl "dec_def", Excl "vyper_decode_valid_enc_def"],
   drule abi_valid_string_source_decode >> strip_tac >>
     qexistsl_tac [`String`, `payload`] >>
     gvs[abi_builtin_valid_bytes_pre_def, abi_builtin_valid_bytes_resources_def,
       Excl "dec_def", Excl "vyper_decode_valid_enc_def"]]
QED

Theorem lower_abi_decode_valid_bytes_source:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type env ty = SOME tv /\ evaluate_abi_decode env ty bs = INL v /\
  lower_abi_decode data (DecBytestring n) min_size max_size
    (abi_decode_bytes_copy_size n) st = (out,final) /\ fn_has_code st final func /\
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
  drule_all abi_builtin_valid_bytes_source_pre >> strip_tac >>
  drule_all lower_abi_decode_valid_bytes >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED
