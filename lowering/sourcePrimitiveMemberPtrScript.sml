(* Physical observations of the same primitive execution used by the ghost port. *)
Theory sourcePrimitiveMemberPtr
Ancestors sourceWordDecoderPtr sourceBytesRepresentation sourceEncodingLayout
  decoderMemberPrefixPtr abiDecoderClampedWord ghostPcTransportPtr
  abiDecoderContract abiDecoderBytes compileEnv venomState words
  abiDecoderCoherence abiDecoderDynamicLoopSetup ptrDiscipline abiDecoderWordTyped
  abiDecoderMemberSetup exprLowering vyperABI vyperTyping abiDecoderClamp
  fragExec list finite_map pred_set arithmetic

Theorem clamped_word_endpoint_physical_frame:
  compile_abi_decode_to_buf dst src opc hi (DecPrimWord clamp) sa = ((),sb) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w srcpos) /\
  eval_operand dst s = SOME (n2w d) /\
  srcpos < dimword (:256) /\ d < dimword (:256) /\
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w srcpos : bytes32) s) /\
  fresh_vars_wrt sa s /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := k) ==>
  abi_decode_frame d 32 s t /\ fresh_vars_wrt sb t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_clamped_word_copied_window >>
  strip_tac >> gvs[] >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def] >> gvs[]
QED

Theorem bytestring_endpoint_physical_frame:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (DecBytestring n) sa = ((),sb) /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME sw /\
  eval_operand dst s = SOME dw /\ abi_decode_load opc sw s = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt sa s /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := k) ==>
  abi_decode_frame (w2n dw) (abi_decode_bytes_copy_size n) s t /\
  fresh_vars_wrt sb t /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all abi_decode_bytes_sentinel_sequence >> strip_tac >>
  gvs[] >> gvs[abi_decode_frame_def, fresh_vars_wrt_def] >> gvs[]
QED

(* The prepared-state certificate concerns only navigation, never the child.
   Both the source value and the ghosts below are produced by execution. *)
Theorem source_word_member_ptr:
  abi_decode_member_setup (Var root) src CALLDATALOAD (Lit 0w)
    dyn ao vo sa = (ops,mid) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) CALLDATALOAD (Lit 0w)
    (DecPrimWord clamp) mid = ((),sb) /\
  lookup_var root s = SOME a /\ not_fresh_at sa root /\
  (!q. src = Var q ==> not_fresh_at sa q) /\
  ptr_covers G tn root s cap /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  vo + 32 <= cap /\ w2n a + vo < dimword (:256) /\
  run_inst_seq (emitted_insts sa mid) s = OK (r with vs_inst_idx := s.vs_inst_idx) /\
  abi_decoder_address_frame sa.cs_next_var s r /\ fresh_vars_wrt mid r /\
  r.vs_current_bb = mid.cs_current_bb /\ r.vs_inst_idx = LENGTH mid.cs_current_insts /\
  eval_operand (FST ops) r = SOME (n2w srcpos) /\ srcpos < dimword (:256) /\
  abi_decoder_coherent ce env sf ty tv /\ is_word_type ty /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  fn_has_code sa mid fn /\ fn_has_code mid sb fn /\ fn_inst_ids_distinct fn /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t H u q.
    SND ops = Var q /\
    run_inst_seq (emitted_insts mid sb) r = OK (t with vs_inst_idx := r.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_covers H u q t 32 /\
    val_in_memory tv v (w2n a + vo) t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v (w2n a + vo) mem) /\
    abi_decode_frame (w2n a + vo) 32 s t /\ fresh_vars_wrt sb t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!op w. abi_decoder_operand_live sa.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lo fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all calldata_member_setup_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  gvs[lookup_var_def] >>
  `abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) r)` by
    (irule coherent_source_word_clamp >> simp[abi_decode_source_def] >> metis_tac[]) >>
  `evaluate_type env ty = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `eval_operand (Var q) r = SOME (n2w (w2n a + vo))` by
    simp[eval_operand_def, lookup_var_def] >>
  `allocas_from lo r /\ ~r.vs_halted` by
    (gvs[abi_decoder_address_frame_def, allocas_from_def] >> gvs[]) >>
  `mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av` by simp[] >>
  drule_all (SRULE [] (Q.INST [`sw` |-> `n2w srcpos : bytes32`]
    calldata_source_word_ptr_endpoint_uniform)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `w2n a + vo < dimword (:256)` by decide_tac >>
  drule_all (SRULE [abi_decode_source_opcode_def]
    (Q.INST [`opc` |-> `CALLDATALOAD`] clamped_word_endpoint_physical_frame)) >>
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at mid x` by
    (drule abi_decode_member_setup_counters >> strip_tac >>
     simp[not_fresh_at_def] >> rpt strip_tac >> gvs[not_fresh_at_def] >>
     Cases_on `dyn` >> gvs[] >> decide_tac) >>
  qexistsl_tac [`s'`, `G'`, `tn'`] >>
  gvs[w2n_n2w, LESS_MOD, abi_decoder_address_frame_def, abi_decode_frame_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `r.vs_inst_idx = _` (fn th => fs[GSYM th]) >>
  qpat_x_assum `s.vs_inst_idx = _` (fn th => fs[GSYM th]) >>
  metis_tac[]
QED
