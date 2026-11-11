Theory entryReachBodyPreludeFrame
Ancestors
  calldataRegistrationExec abiDecoderReentryAddress fragExecMem actualAllocExec
  venomExecProofs emitHelperProps exprLoweringProps finite_map words
  abiDecoderReentry venomState venomExecSemantics abiDecoderContract
  compileEnv emitHelper venomInst arithmetic moduleLowering abiEncoder
  fragExec abiDecoderAppend calldataDynOwned

Definition entry_prelude_frame_def:
  entry_prelude_frame s t <=>
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx /\ t.vs_immutables = s.vs_immutables /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_fmp = s.vs_fmp
End

Theorem entry_prelude_frame_refl[local]:
  entry_prelude_frame s s
Proof
  simp[entry_prelude_frame_def]
QED

Theorem entry_prelude_frame_trans[local]:
  entry_prelude_frame s t /\ entry_prelude_frame t u ==>
  entry_prelude_frame s u
Proof
  simp[entry_prelude_frame_def]
QED

Theorem entry_prelude_frame_update[local]:
  entry_prelude_frame s ((update_var name w s) with vs_inst_idx := idx)
Proof
  simp[entry_prelude_frame_def, update_var_def]
QED

Theorem entry_pure_emit_framed[local]:
  emit_op opc args st = (out,last) /\
  (opc = ADD \/ opc = CALLDATALOAD) /\
  step_inst_base (mk_inst st.cs_next_id opc args
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME w /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    entry_prelude_frame s t
Proof
  strip_tac >> (
  `frag_exec_mem ctx st last (\u. u = s)
    (\u. u = (update_var (STRING #"%" (toString st.cs_next_var)) w s)
      with vs_inst_idx := LENGTH last.cs_current_insts) (\r. F)` by
    (irule registration_emit_step_mem >> goal_assum $ drule_at Any >> simp[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString st.cs_next_var)) w s)
    with vs_inst_idx := LENGTH last.cs_current_insts` >>
  simp[entry_prelude_frame_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  conj_tac
  >- simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
          ASCIInumbersTheory.toString_inj] >>
  gen_tac >> strip_tac >> drule calldata_update_protected >>
  disch_then (qspecl_then [`w`,`s`] mp_tac) >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, update_var_def])
QED

Theorem entry_add_framed[local]:
  emit_op ADD [lhs;rhs] st = (out,last) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME (a+b) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\ entry_prelude_frame s t
Proof
  strip_tac >> irule entry_pure_emit_framed >>
  goal_assum $ drule_at Any >> simp[] >> irule step_ADD >> simp[]
QED

Theorem entry_read_framed[local]:
  emit_op CALLDATALOAD [src] st = (out,last) /\
  eval_operand src s = SOME p ==>
  ?t. frag_exec_mem ctx st last (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand out t = SOME (abi_decode_load CALLDATALOAD p s) /\
    abi_decoder_operand_live last.cs_next_var out /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\ entry_prelude_frame s t
Proof
  strip_tac >> irule entry_pure_emit_framed >>
  goal_assum $ drule_at Any >> simp[] >> irule abi_decode_read_step >>
  simp[abi_decode_source_opcode_def]
QED

Theorem entry_registration_address_prelude_framed:
  emit_op ADD [Lit (n2w 4); Lit (n2w (off-4))] st = (head,after_head) /\
  (if dyn then
    ?offset after_load.
      emit_op CALLDATALOAD [head] after_head = (offset,after_load) /\
      emit_op ADD [Lit (n2w 4); offset] after_load = (src,first)
   else src = head /\ first = after_head) ==>
  ?t. frag_exec_mem ctx st first (\u. u = s) (\u. u = t) (\r. F) /\
    eval_operand src t = SOME
      (if dyn then n2w 4 + abi_decode_load CALLDATALOAD
         (n2w 4 + n2w (off-4):bytes32) s else n2w 4 + n2w (off-4)) /\
    abi_decoder_operand_live first.cs_next_var src /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    entry_prelude_frame s t
Proof
  strip_tac >>
  `eval_operand (Lit (n2w 4)) s = SOME (n2w 4) /\
   eval_operand (Lit (n2w (off-4))) s = SOME (n2w (off-4))` by
    simp[eval_operand_def] >>
  drule_all entry_add_framed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  reverse (Cases_on `dyn`) >- (gvs[] >> goal_assum $ drule_at Any >> simp[]) >>
  gvs[] >> drule_all entry_read_framed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) t =
   abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) s` by
    fs[entry_prelude_frame_def, abi_decode_load_def, abi_decode_source_def] >>
  `eval_operand (Lit (n2w 4)) t' = SOME (n2w 4)` by simp[eval_operand_def] >>
  drule_all entry_add_framed >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `cs_extends st after_head /\ cs_extends after_head after_load /\
   cs_extends after_load first` by
    (imp_res_tac emit_op_extends >> rpt conj_tac >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `frag_exec_mem ctx st after_load (\u. u = s) (\u. u = t') (\r. F)` by
    (irule frag_exec_mem_seq >> goal_assum $ drule_at Any >> simp[] >>
     goal_assum $ drule_at Any >> simp[]) >>
  `frag_exec_mem ctx st first (\u. u = s) (\u. u = t'') (\r. F)` by
    (irule frag_exec_mem_seq >> qexistsl_tac [`\u. u = t'`, `after_load`] >>
     simp[] >> metis_tac[cs_extends_trans]) >>
  `entry_prelude_frame s t''` by metis_tac[entry_prelude_frame_trans] >>
  qexists_tac `t''` >> simp[] >>
  gen_tac >> strip_tac >>
  `st.cs_next_var <= after_head.cs_next_var /\
   after_head.cs_next_var <= after_load.cs_next_var` by
    metis_tac[emitted_insts_emit_op, LESS_EQ_ADD] >>
  metis_tac[abi_decoder_operand_live_mono]
QED
