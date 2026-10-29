Theory abiBuiltinEncodeFinish
Ancestors
  abiBuiltinEncodeCode abiEncoderWrites abiBuiltinPrefix abiEncoderBytesPrefix
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderReentryAddress abiDecoderFrameCompose
  abiDecoderFrame abiDecoderArrayInitExec abiDecoderContract abiDecoderGuards
  abiDecoderArrayHeader emitHelperProps exprLoweringProps compileEnv emitHelper venomState
  venomExecSemantics venomMemProps words list arithmetic abiEncoderSequence
  abiDecoderCorrectWord abiDecoderEffect abiDecoderLoop fragExec instIdxIndep

(* ===== Sequence ===== *)

(* Execute the actual builtin length store, preserving old operands and all
   memory outside the length word. Supports a method-ID prefix of any size. *)

Theorem abi_builtin_store_sequence:
  emit_void MSTORE [buf;value_op] st = ((),final) /\
  eval_operand buf s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq (emitted_insts st final) s = OK (mstore p w s) /\ inst_extends st final /\
  fresh_vars_wrt limit_st (mstore p w s) /\ mload p (mstore p w s) = w /\
  abi_decode_frame p 32 s (mstore p w s) /\
  (mstore p w s).vs_allocas = s.vs_allocas /\
  (mstore p w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore p w s).vs_halted = s.vs_halted /\
  (!op. eval_operand op (mstore p w s) = eval_operand op s)
Proof
  strip_tac >> drule_all abi_encoder_emit_store >>
  simp[abi_decode_mstore_frame, mload_mstore_same, eval_operand_mstore]
QED

Theorem abi_builtin_encode_finish_sequence:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    fresh_vars_wrt limit_st actual /\ mload p actual = n2w (len+mid_size) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  Cases_on `mid_size > 0`
  >- (asm_simp_tac bool_ss [abi_builtin_encode_finish_def, comp_bind_def, LET_THM] >>
      pairarg_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
      rename1 `emit_op ADD [encoded_len;Lit (n2w mid_size)] st = (total_op,prepared_st)` >>
      imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
      `prepared_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
      mp_tac (Q.INST [`lhs` |-> `encoded_len`, `rhs` |-> `Lit (n2w mid_size)`,
        `out` |-> `total_op`, `a` |-> `n2w len:bytes32`, `b` |-> `n2w mid_size:bytes32`,
        `st'` |-> `prepared_st`, `s` |-> `initial:venom_state`] abi_builtin_emit_add) >>
      impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
      rename1 `abi_builtin_prefix st prepared_st limit_st initial prepared` >>
      `eval_operand buf prepared = SOME (n2w p)` by
        (drule_all abi_encoder_prefix_eval >> simp[]) >>
      qpat_assum `abi_builtin_prefix _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
      mp_tac (Q.INST [`value_op` |-> `total_op`, `st` |-> `prepared_st`,
        `s` |-> `prepared:venom_state`, `w` |-> `n2w (len+mid_size):bytes32`] abi_builtin_store_sequence) >>
      impl_tac >- asm_simp_tac (srw_ss()) [word_add_n2w] >> strip_tac >>
      `run_inst_seq (emitted_insts st final) initial = OK (mstore p (n2w (len+mid_size)) prepared) /\
       inst_extends st final` by
        (mp_tac (Q.INST [`st1` |-> `prepared_st`, `st2` |-> `final`,
          `s` |-> `initial:venom_state`, `s1` |-> `prepared:venom_state`,
          `s2` |-> `mstore p (n2w (len+mid_size)) prepared`] abi_decode_sequence_chain) >>
         asm_simp_tac bool_ss []) >>
      qpat_assum `abi_decoder_address_frame _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
      `abi_decode_frame p 32 initial (mstore p (n2w (len+mid_size)) prepared)` by
        (irule abi_decode_frame_trans >> qexists_tac `prepared` >>
         asm_simp_tac bool_ss [abi_decode_frame_def]) >>
      qexists_tac `mstore p (n2w (len+mid_size)) prepared` >> asm_simp_tac bool_ss [] >>
      rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `mid_size = 0` by decide_tac >> gvs[abi_builtin_encode_finish_def] >> strip_tac >>
  drule_all abi_builtin_store_sequence >> strip_tac >>
  qexists_tac `mstore p (n2w len) initial` >> asm_simp_tac bool_ss []
QED

(* ===== Builtin Encode Finish ===== *)

(* The actual length store reaches its containing-function endpoint and
   preserves both the method-ID bytes and completed ABI payload. *)

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
