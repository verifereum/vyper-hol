(* Generic output allocation, normalized to the encoder phase interface. *)
Theory abiEncodeAllocationPhase
Ancestors
  abiEncoderWindowPhase abiEncoderWindowSequence abiEncoderWindowContract
  abiEncoderRegisteredEffect externalReturnNormalizeRun actualAllocExec
  allocaSiteResource loweringHalt exprLoweringProps emitHelperProps
  compileEnv emitHelper fragExec venomState venomExecSemantics venomInst
  finite_map words list rich_list arithmetic pred_set

Theorem abi_encode_alloc_sequence[local]:
  compile_alloc_buffer n st = (buf,en) /\
  exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) s (n2w n : bytes32) = OK t ==>
  window_seq st en s t
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts st en = [mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq (emitted_insts st en) s = OK t` by
    (simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_read1_def, eval_operands_def, eval_operand_def] >>
     qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >> simp[mk_inst_def]) >>
  simp[window_seq_def, inst_extends_def, mk_inst_def, is_terminator_def,
    IS_PREFIX_APPEND] >> rpt strip_tac >>
  `x <> STRING #"%" (toString st.cs_next_var)` by metis_tac[] >>
  qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
  simp[exec_alloca_def, mk_inst_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  simp[AllCaseEqs(), LET_THM] >> strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_encode_alloc_window_phase:
  compile_alloc_buffer n st = (buf,en) /\ fn_has_code st en func /\
  alloca_room ctx func s /\ alloca_inv s /\ n < dimword (:256) /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = n) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u d. window_phase ctx func st en {st.cs_next_id} [] s u /\
    mem_cont_sim ctx func s u /\
    eval_operand buf.buf_operand u = SOME (n2w d) /\
    (!q. buf.buf_operand = Var q ==> not_fresh_at en q) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (d,n) /\
    d+n <= u.vs_alloca_next /\ d+n < dimword (:256) /\
    u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_data_section = s.vs_data_section
Proof
  strip_tac >> drule_all actual_alloc_buffer_site >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w n)] /\
   inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
   inst.inst_id = st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `!b sz. FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = w2n (n2w n : bytes32)` by simp[] >>
  drule_all alloca_site_execute >> strip_tac >>
  drule_all actual_literal_alloca_frame >> strip_tac >>
  `window_alloca_growth s t` by (drule_all window_exec_alloca_growth >> simp[]) >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s t` by
    (drule_all window_exec_alloca_effect >> simp[]) >>
  `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) s (n2w n : bytes32) = OK t` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >> simp[Abbr `inst`]) >>
  drule_all abi_encode_alloc_sequence >> strip_tac >>
  drule_all normalize_alloc_mem_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `window_phase ctx func st en {st.cs_next_id} [] s
     (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule window_seq_phase >> simp[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `b+n < dimword (:256)` by (drule alloca_room_next_lt >>
      qpat_x_assum `b + w2n _ <= _` mp_tac >> simp[] >> decide_tac) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `b`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qpat_x_assum `buf.buf_operand = _` SUBST1_TAC >>
      qpat_x_assum `lookup_var _ t = _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[eval_operand_def, lookup_var_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`b + w2n _ <= _`, `FLOOKUP t.vs_allocas inst.inst_id = _`,
     `inst.inst_id = _`, `n < dimword (:256)`, `buf.buf_operand = _`,
     `not_fresh_at en _`, `b+n < dimword (:256)`,
     `t.vs_memory = _`, `t.vs_call_ctx = _`, `t.vs_data_section = _`] >>
  rpt (pop_assum kall_tac) >> simp[]
QED
