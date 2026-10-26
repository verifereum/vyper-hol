(* The actual length store reaches its containing-function endpoint and
   preserves both the method-ID bytes and completed ABI payload. *)
Theory abiBuiltinEncodeFinish
Ancestors
  abiBuiltinEncodeFinishSequence abiBuiltinEncodeCode abiEncoderSequenceReach abiEncoderWrites
  abiDecoderCorrectWord abiDecoderEffect abiDecoderFrameCompose abiDecoderFrame
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderArrayInitExec abiDecoderContract
  abiDecoderLoop fragExec instIdxIndep compileEnv venomState words list arithmetic

Theorem abi_builtin_encode_finish_reach:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule_all abi_builtin_encode_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_builtin_encode_finish:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ 32 <= output_size /\
  (p+output_size <= b \/ b+cap <= p) /\ abi_decoder_budget first last b cap initial /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    (!q n. p+32 <= q ==> mem_bytes_at q n actual.vs_memory = mem_bytes_at q n initial.vs_memory) /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_finish_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_frame p output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`p`, `32`] >> asm_simp_tac (srw_ss()) []) >>
  `abi_decoder_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual` by
    (irule abi_decoder_scratch_free_effect >> asm_simp_tac (srw_ss()) []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_assum `abi_decode_frame p 32 initial actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_FINISH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin encoder finish not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeFinish");
