(* Allocation-free encoder counting does not consume interval scratch credit. *)
Theory bodyIntCallEncoderActualCopy
Ancestors
  bodyIntCallDecoderCountedPrimitive abiEncoderReentryLeaves abiEncoderLeafCode
  abiEncoderAdmissible abiDecoderContract abiDecoderFrame abiDecoderLoop
  exprLoweringProps emitHelperProps compileEnv fragGasPath venomState
  venomExecSemantics venomInst instIdxIndep valueEncoding contractABI
  words list rich_list entrySinkExtraction

Theorem intcall_encoder_copy_counted_no_budget:
  compile_abi_encode_to_buf dst src (AbiCopy sz) st = (out,st') /\
  abi_encoder_input (AbiCopy sz) at av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  sb < dimword (:256) /\ d < dimword (:256) /\ sz < dimword (:256) /\
  fresh_vars_wrt limit_st initial /\ fn_has_code st st' func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n.
    mem_bytes_at d (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc at av))) /\
    fresh_vars_wrt limit_st actual /\
    abi_decode_frame d (LENGTH (enc at av)) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  strip_tac >>
  `abi_encoder_static_leaf (AbiCopy sz)` by simp[abi_encoder_static_leaf_def] >>
  drule_all abi_encode_static_leaf_shape >> strip_tac >>
  drule_all abi_encoder_copy_input_reentry >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >> fs[abi_decode_frame_def, fresh_vars_wrt_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED
