(* Repeatable calldata decoder steps: operand liveness, single CALLDATALOAD
   reads, ADD/MUL steps and the array-header load-and-store.  The rest of the
   former dynamic-calldata ownership spine was removed as dead. *)
Theory calldataDynOwned
Ancestors
  actualAllocExec fragExecMem
  allocaFrontierBound allocaBudgetProps abiDecoderIndexInit abiDecoderContract
  compileEnv emitHelper venomState venomInst venomExecSemantics venomMemProps venomMemDefs
  valueEncodingProps finite_map words arithmetic list rich_list
  abiDecoderIndexedAddress abiDecoderReentryAddress abiDecoderReentry
  abiDecoderGuards abiDecoderFrame emitHelperProps exprLoweringProps abiEncoder
  abiDecoderExecution valueEncoding instIdxIndep
  abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs
  abiDecoderLoopEmit abiDecoderCounters abiDecoderDynarrayPrefix
  abiDecoderDynarrayBound abiDecoderArrayHeader abiDecoderReservation
  abiDecoderArrayLoopInit abiDecoderFrameCompose

(* Syntactic protection, unlike fresh_vars_wrt, is repeatable. *)
Theorem calldata_operand_live_not_fresh:
  abi_decoder_operand_live st.cs_next_var (Var x) <=> not_fresh_at st x
Proof
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]
QED

Theorem calldata_update_protected:
  abi_decoder_operand_live next op ==>
  eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> first_x_assum (qspec_then `next` mp_tac) >> simp[]
QED

Theorem calldata_binary_repeat:
  emit_op opc [lhs;rhs] st = (out,st') /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (if opc = ADD then a+b else a*b) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t = update_var (STRING #"%" (toString st.cs_next_var))
      (if opc = ADD then a+b else a*b) s /\ inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (if opc = ADD then a+b else a*b) s` >>
  `step_inst_base (mk_inst st.cs_next_id opc [lhs;rhs]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (gvs[Abbr `t`] >> FIRST [irule step_ADD, irule step_MUL] >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_read_repeat:
  emit_op CALLDATALOAD [src] st = (out,st') /\ eval_operand src s = SOME p ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (abi_decode_load CALLDATALOAD p s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t = update_var (STRING #"%" (toString st.cs_next_var))
      (abi_decode_load CALLDATALOAD p s) s /\ inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (abi_decode_load CALLDATALOAD p s) s` >>
  `step_inst_base (mk_inst st.cs_next_id CALLDATALOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_decode_read_step >>
     simp[abi_decode_source_opcode_def]) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_array_header_repeat_sequence:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ d < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD p s) /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    abi_decode_frame d 32 s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st'
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),last_st)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK loaded` >>
  `eval_operand dst loaded = SOME (n2w d)` by metis_tac[] >>
  `run_inst_seq (emitted_insts c1 last_st) loaded =
     OK (mstore d (abi_decode_load CALLDATALOAD p s) loaded)` by
    (`step_inst_base (mk_inst c1.cs_next_id MSTORE [dst;cnt] []) loaded =
       OK (mstore (w2n (n2w d : bytes32)) (abi_decode_load CALLDATALOAD p s) loaded)` by
       (irule step_MSTORE >> simp[]) >>
     `w2n (n2w d : bytes32) = d` by simp[] >>
     drule emitted_insts_emit_void >> strip_tac >>
     qpat_x_assum `loaded = _` kall_tac >> fs[run_inst_seq_def]) >>
  drule inst_extends_emit_void >> strip_tac >>
  qexists_tac `mstore d (abi_decode_load CALLDATALOAD p s) loaded` >>
  conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`loaded`,`c1`] >> simp[]) >>
  qpat_x_assum `loaded = _` kall_tac >>
  simp[eval_operand_mstore, mstore_mem_word_at_same] >>
  conj_tac
  >- (`abi_decode_frame d 32 loaded
         (mstore d (abi_decode_load CALLDATALOAD p s) loaded)` by
        irule abi_decode_mstore_frame >>
      qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
      simp[abi_decode_frame_def]) >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  metis_tac[inst_extends_trans]
QED
