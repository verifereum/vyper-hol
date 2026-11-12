(* Finite fetched execution for the nonrecursive source-labelled endpoints.
   Head bounds and actual output extents remain explicit caller obligations. *)
Theory abiDecoderPrimitiveFetched
Ancestors
  loweringStateRelDefs
  abiDecoderScalarOutcome abiDecoderBytestringSource abiDecoderSequenceReach
  abiDecoderClampedWord abiDecoderWordOutcome abiDecoderBytesTyped
  abiDecoderBytesPhases abiDecoderSiteEffect abiDecoderContract
  exprLoweringProps compileEnv venomState venomInst venomExecSemantics
  instIdxIndep valueEncoding vyperValue vyperABI contractABI words list rich_list

Theorem abi_decoder_scalar_fetched_outcome:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand hi s = SOME (n2w H) /\ pos+32 <= H /\
  B+H < dimword (:256) /\ d+32 < dimword (:256) /\
  fresh_vars_wrt st s /\ abi_decoder_clamp_wf clamp /\
  decode_site_resources ctx fn s /\ {a | d <= a /\ a < d+32} SUBSET writes /\
  d+32 <= s.vs_alloca_next /\ assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  bs = mem_bytes_at (B+pos) 32 (abi_decode_source opc s) /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((?t v. decoder_straight_prefix func s t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v /\
    val_in_memory tv v d t.vs_memory /\
    mem_word_at d t.vs_memory = abi_decode_load opc (n2w (B+pos):bytes32) s /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
   (?encoded n. run_inst_seq (emitted_insts st st') s = Abort Revert_abort encoded /\
    run_from 0 ctx func s = Abort Revert_abort (encoded with vs_inst_idx := n) /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
      ?v. abi_to_vyper env ty (dec (vyper_to_abi_type env ty) bs) = SOME v)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  drule_all abi_decoder_word_inst_extends >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all abi_decoder_scalar_source_outcome >>
  disch_then (qspec_then `next` strip_assume_tac)
  >- (disj1_tac >>
      drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      qexistsl_tac [`t'`,`v`] >>
      gvs[fresh_vars_wrt_def, eval_op_inst_idx]) >>
  disj2_tac >> drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Theorem abi_decoder_bytestring_fetched_outcome:
  compile_abi_decode_to_buf dst pos MLOAD base_op hi (DecBytestring n) st = ((),st') /\
  base_op <> Lit 0w /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\ eval_operand base_op s = SOME (n2w b) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand hi s = SOME (n2w h) /\
  c = w2n (abi_decode_load MLOAD (n2w (b+p):bytes32) s) /\
  p < dimword (:256) /\ b+h < dimword (:256) /\
  d+abi_decode_bytes_copy_size n < dimword (:256) /\
  (b+h <= d \/ d+abi_decode_bytes_copy_size n <= b) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx fn s /\
  {a | d <= a /\ a < d+abi_decode_bytes_copy_size n} SUBSET writes /\
  d+abi_decode_bytes_copy_size n <= s.vs_alloca_next /\
  bs = mem_bytes_at (b+p) (h-p) s.vs_memory /\
  (bt = BytesT (Dynamic n) \/ bt = StringT n) /\
  fn_has_code st st' func /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((?t v. decoder_straight_prefix func s t /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    vyper_decode_valid_enc (vyper_to_abi_type env (BaseT bt)) bs /\
    abi_to_vyper env (BaseT bt) (dec (vyper_to_abi_type env (BaseT bt)) bs) = SOME v /\
    val_in_memory (BaseTV bt) v d t.vs_memory /\ fresh_vars_wrt st' t /\
    mem_bytes_at d (32+c) t.vs_memory = mem_bytes_at (b+p) (32+c) s.vs_memory /\
    mem_bytes_at (d+32+c) (32*((c+31) DIV 32)-c) t.vs_memory =
      REPLICATE (32*((c+31) DIV 32)-c) 0w /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    decode_site_effect ctx fn next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next) \/
   (?encoded ix. run_inst_seq (emitted_insts st st') s = Abort Revert_abort encoded /\
    run_from 0 ctx func s = Abort Revert_abort (encoded with vs_inst_idx := ix) /\
    ~(vyper_decode_valid_enc (vyper_to_abi_type env (BaseT bt)) bs /\
      ?v. abi_to_vyper env (BaseT bt)
        (dec (vyper_to_abi_type env (BaseT bt)) bs) = SOME v)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  `inst_extends st st'` by
    (drule_all abi_decode_bytes_position_shape >> simp[]) >>
  drule_all abi_decoder_bytestring_source_outcome >>
  disch_then (qspecl_then [`next`,`env`] strip_assume_tac)
  >- (disj1_tac >>
      drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      qexistsl_tac [`t'`,`v`] >>
      gvs[fresh_vars_wrt_def, eval_op_inst_idx]) >>
  disj2_tac >> drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED
