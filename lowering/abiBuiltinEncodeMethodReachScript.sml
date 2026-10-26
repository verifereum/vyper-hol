(* The actual full-word method-ID store yields its four-byte prefix at the
   containing-function endpoint, with the exact full-word write frame. *)
Theory abiBuiltinEncodeMethodReach
Ancestors
  abiBuiltinEncodeMethod abiEncoderMemory abiEncoderSequenceReach abiDecoderTypedContract
  abiDecoderReentry abiDecoderContract abiDecoderLoop abiDecoderDynamicLoopSetup
  fragExec instIdxIndep compileEnv valueEncodingProps venomState venomExecSemantics
  words byte list rich_list arithmetic

Definition abi_builtin_encode_method_bytes_def:
  abi_builtin_encode_method_bytes (mid:bytes32) = TAKE 4 (word_to_bytes (mid << 224) T)
End

Theorem abi_builtin_encode_method_bytes_length[simp]:
  LENGTH (abi_builtin_encode_method_bytes mid) = 4
Proof
  simp[abi_builtin_encode_method_bytes_def, LENGTH_word_to_bytes]
QED

Theorem abi_builtin_encode_method_window:
  mload p s = mid << 224 ==>
  mem_bytes_at p 4 s.vs_memory = abi_builtin_encode_method_bytes mid
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`p`, `[]:byte list`, `TAKE 4 (word_to_bytes ((mid:bytes32) << 224) T)`,
    `DROP 4 (word_to_bytes ((mid:bytes32) << 224) T)`, `s.vs_memory`]
    abi_decoder_source_subwindow) >>
  asm_simp_tac (srw_ss()) [TAKE_DROP, LENGTH_word_to_bytes, LENGTH_TAKE,
    abi_encoder_word_window, mem_word_at_eq_mload, abi_builtin_encode_method_bytes_def]
QED

Theorem abi_builtin_encode_method_reach:
  abi_builtin_encode_method_id (SOME mid) buf st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ p+32 < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes mid /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame (p+32) 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_method_shape >> strip_tac >>
  drule_all abi_builtin_encode_method_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  drule abi_builtin_encode_method_window >> strip_tac >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx] >> first_assum ACCEPT_TAC
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_METHOD_REACH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin method-ID reach not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeMethodReach");
