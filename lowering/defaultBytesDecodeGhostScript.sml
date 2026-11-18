(* One horizon-independent ghost endpoint for successful calldata bytes decoding. *)
Theory defaultBytesDecodeGhost
Ancestors calldataDecodePtr calldataBytesLive abiDecoderBytes fragGasOriginPtrLoop
  fragGasSeqPtr fragExecMem venomState venomExecSemantics bodyPtrDefs
  ptrDiscipline ptrSafeRun compileEnv codegenRel emitHelper abiDecoderContract
  decoderGhostFramePtr words list arithmetic finite_map pred_set

Theorem default_bytes_decode_origin:
  compile_abi_decode_to_buf (Var p) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecBytestring maxn) sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  not_fresh_at sa p /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  run_inst_seq (emitted_insts sa sb) s = OK actual /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  inst_extends sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts sa sb) /\
  abi_decode_bytes_copy_size maxn < dimword (:256) /\ maxn < dimword (:256) /\
  ptr_covers G tn p s (abi_decode_bytes_copy_size maxn) /\ op_taint tn src = {} /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    (!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s H u) /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
      (s,G,tn) []
      (OK (actual with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    ptr_covers H u p (actual with vs_inst_idx := LENGTH sb.cs_current_insts)
      (abi_decode_bytes_copy_size maxn) /\
    (!i. w2n dw <= i /\ i < w2n dw + abi_decode_bytes_copy_size maxn ==> i NOTIN u.t_mem) /\
    u.t_mem SUBSET tn.t_mem /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u
       (actual with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `w2n (abi_decode_load CALLDATALOAD sw s) <= maxn` by
    (spose_not_then assume_tac >>
     `maxn < w2n (abi_decode_load CALLDATALOAD sw s)` by decide_tac >>
     drule_all calldata_bytes_rejected_live >> gvs[]) >>
  `abi_decode_load CALLDATALOAD sw s =
    n2w (w2n (abi_decode_load CALLDATALOAD sw s))` by simp[] >>
  `abi_decode_bytes_copy_size maxn = 32 + 32 * ((maxn+31) DIV 32)` by
    simp[abi_decode_bytes_copy_size_def] >>
  drule_all calldata_bytestring_overwrite_endpoint_core_uniform_sequence_joint >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `s' = actual with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (gvs[] >> simp[venom_state_component_equality]) >>
  qexistsl_tac [`G'`,`tn'`] >> gvs[] >>
  rpt gen_tac >> irule emitted_origin_ptr_path >> simp[] >>
  qexists_tac `sa` >> simp[]
QED
