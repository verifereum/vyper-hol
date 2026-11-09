Theory exprSimAbiEncodeTupleStagingProbe
Ancestors
  exprSimAbiEncodeTupleFresh exprSimAbiEncodeTupleSuccess
  exprSimAbiEncodeExtension abiEncoderExtendSim abiDecoderVarExtend
  abiDecoderReentry freshWrites abiDecoderContract
  compileEnv venomState venomInst list

(* The argument contract restricts without changing its original baseline. *)
Theorem abi_encode_tuple_clean_args_probe:
  abi_args_post ctx func ce cx es origin st s0 es' args ops vs initial /\
  EVERY (abi_decoder_operand_live st.cs_next_var) ops /\
  local_ptrs_reserved ce st /\ origin.cs_next_var <= st.cs_next_var /\
  st.cs_next_var <= final.cs_next_var ==>
  abi_args_post ctx func ce cx es origin st s0 es' args ops vs (drop_fresh st initial) /\
  fresh_vars_wrt final (drop_fresh st initial)
Proof
  strip_tac >> conj_tac
  >- (irule abi_encode_args_post_drop_fresh >> asm_rewrite_tac []) >>
  irule abi_encode_drop_final_fresh >> asm_rewrite_tac []
QED

(* Staging is a concrete straight-line sequence: lift the raw execution,
   then count the lifted run, rather than attempting to lift a counted path. *)
Theorem abi_encode_tuple_clean_staging_probe:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st staged) (drop_fresh st initial) = OK clean ==>
  ?actual. run_inst_seq (emitted_insts st staged) initial = OK actual /\
    abi_decoder_vars_extend initial.vs_vars clean actual /\
    gas_marked_path F ctx func initial 0
      (OK (actual with vs_inst_idx := LENGTH staged.cs_current_insts)) /\
    ~actual.vs_halted /\ actual.vs_current_bb = staged.cs_current_bb
Proof
  strip_tac >> drule_all abi_encode_tuple_stage_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts st staged)` by
    (fs[EVERY_MEM] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `abi_decoder_vars_extend initial.vs_vars (drop_fresh st initial) initial` by
    simp[abi_encode_drop_fresh_bounded_extension] >>
  drule_all abi_encoder_sequence_extend >> strip_tac >>
  drule_all abi_encode_tuple_staging_path >> strip_tac >>
  goal_assum (drule_at Any) >> asm_rewrite_tac []
QED
