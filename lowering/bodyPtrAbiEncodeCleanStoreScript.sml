(* A clean store changes only its explicit memory/taint window. *)
Theory bodyPtrAbiEncodeCleanStore
Ancestors
  bodyPtrAbiEncodeCursorFrame bodyPtrDefs typedCopyPtr fragGasSeqPtr fragGasPathPtr emitHelperProps
  venomExecSemantics venomState ptrDiscipline ptrSafeRun finite_map
  compileEnv list rich_list arithmetic venomInst fragExecPtr words exprLoweringProps
  abiDecoderReentry abiDecoderContract bodyPtrAbiEncodeWordChecks pred_set

Theorem abi_encode_clean_store_sequence:
  emit_void MSTORE [Var dst;value] st = ((),en) /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  ~ctx_has_dalloca ctx ==>
  run_inst_seq (emitted_insts st en) s = OK (mstore (w2n a) w s) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st en) s G
    (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32})
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id MSTORE [Var dst;value] []) s =
     OK (mstore (w2n a) w s)` by
    simp[Once step_inst_base_def, mk_inst_def, exec_write2_def, eval_operand_def] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst st.cs_next_id MSTORE [Var dst;value] []) s` by
    (irule ptr_inst_ok_mstore >> simp[]) >>
  drule_all mstore_ghost_frame >>
  disch_then (qspecl_then [`PG`, `G`, `st.cs_next_id`] strip_assume_tac) >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >>
  simp[taint_component_equality, step_taint_def, mk_inst_def,
       set_var_taint_def, adopt_reset_def, imm_taint_def]
QED

Theorem abi_encode_clean_store_checked_path:
  emit_void MSTORE [Var dst;value] st = ((),en) /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G
    (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32})
    (OK ((mstore (w2n a) w s) with vs_inst_idx := s.vs_inst_idx+1))
Proof
  strip_tac >> drule_all abi_encode_clean_store_sequence >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]
QED

Theorem abi_encode_read_frame_store:
  abi_encode_read_frame st s G tn t H un ==>
  abi_encode_read_frame st (mstore a w s) G
    (tn with t_mem := tn.t_mem DIFF {i | a <= i /\ i < a+32})
    ((mstore a w t) with vs_inst_idx := k) H
    (un with t_mem := un.t_mem DIFF {i | a <= i /\ i < a+32})
Proof
  simp[abi_encode_read_frame_def, mstore_def, lookup_var_def, op_taint_def]
QED

Theorem abi_encode_clean_store_covers:
  ptr_covers G tn q s n ==>
  ptr_covers G (tn with t_mem := tn.t_mem DIFF removed) q
    ((mstore a w s) with vs_inst_idx := k) n
Proof
  simp[ptr_covers_def, mstore_def, lookup_var_def, op_taint_def]
QED

Theorem abi_encode_clean_store_fresh:
  fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st ((mstore a w s) with vs_inst_idx := k)
Proof
  simp[fresh_vars_wrt_def, mstore_def, lookup_var_def]
QED

Theorem abi_encode_read_frame_weaken:
  abi_encode_read_frame mid s G tn t H un /\
  st.cs_next_var <= mid.cs_next_var ==>
  abi_encode_read_frame st s G tn t H un
Proof
  simp[abi_encode_read_frame_def] >> rpt strip_tac >>
  `not_fresh_at mid q` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  metis_tac[]
QED

Theorem abi_encode_read_frame_pc[simp]:
  abi_encode_read_frame st (s with vs_inst_idx := k) G tn t H un <=>
  abi_encode_read_frame st s G tn t H un
Proof
  simp[abi_encode_read_frame_def, lookup_var_def]
QED

Theorem abi_encode_read_frame_eval:
  abi_encode_read_frame st s G tn t H un /\
  abi_decoder_operand_live st.cs_next_var op ==>
  eval_operand op t = eval_operand op s
Proof
  Cases_on `op` >>
  simp[eval_operand_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def,
    abi_encode_read_frame_def, not_fresh_at_def] >> metis_tac[]
QED
