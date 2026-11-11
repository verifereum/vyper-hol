(* Registered allocation and selector initialization for custom errors. *)
Theory stmtSimCustomErrorPrefix
Ancestors
  abiEncoderWindowPhase memContinuation emitHelperProps loweringStateRelDefs
  externalReturnNormalizeRun windowPhaseMem abiEncoderWindowContract
  abiEncoderPrimitiveEffect abiEncoderRegisteredEffect actualAllocExec
  allocaSiteResource loweringHalt exprLoweringProps compileEnv context
  venomExecSemantics venomState venomInst venomMemDefs
  finite_map words list pred_set arithmetic

Theorem custom_error_allocation_run:
  compile_alloc_buffer n st = (buf,en) /\ fn_has_code st en func /\
  alloca_room ctx func s /\ alloca_inv s /\ n < dimword (:256) /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = n) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u d. mem_cont_sim ctx func s u /\ ~u.vs_halted /\
    u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME (n2w d) /\
    (!q. buf.buf_operand = Var q ==> not_fresh_at en q) /\
    FLOOKUP u.vs_allocas st.cs_next_id = SOME (d,n) /\
    d+n <= u.vs_alloca_next /\ d+n < dimword (:256) /\
    alloca_room ctx func u /\ alloca_inv u /\
    u.vs_memory = s.vs_memory /\
    (!op. (!x. op = Var x ==> not_fresh_at st x) ==>
      eval_operand op u = eval_operand op s) /\
    abi_encoder_registered_effect {st.cs_next_id} [] s u
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
  `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) s (n2w n : bytes32) = OK t` by
    (qpat_assum `exec_alloca _ _ _ = _` mp_tac >> simp[Abbr `inst`]) >>
  drule_all normalize_alloc_mem_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `abi_encoder_registered_effect {st.cs_next_id} [] s t` by
    metis_tac[window_exec_alloca_effect] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `b`] >>
  simp_tac (srw_ss()) [] >>
  suspend "endpoint"
QED

Resume custom_error_allocation_run[endpoint]:
  `b + n < dimword (:256)` by
    (drule alloca_room_next_lt >>
     metis_tac[w2n_n2w, LESS_MOD, LESS_EQ_LESS_TRANS]) >>
  `alloca_room ctx func (t with vs_inst_idx := LENGTH en.cs_current_insts)` by
    (irule alloca_room_fields >> qexists_tac `t` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (qpat_x_assum `(_ with vs_inst_idx := _).vs_current_bb = _` mp_tac >> simp_tac (srw_ss()) []) >>
  conj_tac >- (qpat_x_assum `buf.buf_operand = _` SUBST1_TAC >> simp_tac (srw_ss()) [eval_operand_def] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_x_assum `buf.buf_operand = _` SUBST1_TAC >>
    simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[w2n_n2w, LESS_MOD] >>
  conj_tac >- metis_tac[w2n_n2w, LESS_MOD] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `op <> Var (STRING #"%" (toString st.cs_next_var))` by metis_tac[] >>
      metis_tac[]) >>
  qpat_x_assum `abi_encoder_registered_effect _ _ s t` mp_tac >>
  simp_tac (srw_ss()) [abi_encoder_registered_effect_def]
QED
Finalise custom_error_allocation_run

Theorem custom_error_selector_prefix_run:
  compile_alloc_buffer (B+32) st = (buf,mid) /\
  emit_void MSTORE [buf.buf_operand; Lit selector] mid = ((),en) /\
  fn_has_code st mid func /\ fn_has_code mid en func /\
  alloca_room ctx func s /\ alloca_inv s /\ B+32 < 2 ** 64 /\
  (!b sz. FLOOKUP s.vs_allocas st.cs_next_id = SOME (b,sz) ==> sz = B+32) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t d. mem_cont_sim ctx func s t /\ ~t.vs_halted /\
    t.vs_current_bb = en.cs_current_bb /\
    t.vs_inst_idx = LENGTH en.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w d) /\
    (!q. buf.buf_operand = Var q ==> not_fresh_at en q) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (d,B+32) /\
    d+(B+32) <= t.vs_alloca_next /\ d+(B+32) < dimword (:256) /\
    alloca_room ctx func t /\ alloca_inv t /\
    (!op. (!x. op = Var x ==> not_fresh_at st x) ==>
      eval_operand op t = eval_operand op s) /\
    abi_encoder_registered_effect {st.cs_next_id} [] s t
Proof
  strip_tac >>
  `B+32 < dimword (:256)` by
    (qpat_x_assum `B+32 < 2 ** 64` mp_tac >>
     simp_tac (srw_ss()) [dimword_def] >> decide_tac) >>
  drule_all custom_error_allocation_run >>
  disch_then (qx_choose_then `u` (qx_choose_then `d` strip_assume_tac)) >>
  `abi_encoder_registered_effect {st.cs_next_id} [] u (mstore d selector u)` by
    (irule abi_encoder_registered_effect_mstore >> simp_tac (srw_ss()) [] >>
     rpt strip_tac >>
     qpat_x_assum `!b sz. FLOOKUP u.vs_allocas _ = _ ==> _`
       (qspecl_then [`d`,`B+32`] mp_tac) >>
     asm_rewrite_tac[] >> decide_tac) >>
  `eval_operand (Lit selector) u = SOME selector /\
   d < dimword (:256) /\ d+32 <= u.vs_alloca_next` by
    (simp_tac (srw_ss()) [eval_operand_def] >> decide_tac) >>
  drule_all window_store_phase_mem >> strip_tac >>
  qmatch_asmsub_abbrev_tac `window_phase ctx func mid en _ _ u t` >>
  qexistsl_tac [`t`,`d`] >>
  suspend "handoff"
QED

Resume custom_error_selector_prefix_run[handoff]:
  drule window_phase_control >> strip_tac >>
  drule window_phase_resources >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  conj_tac >- metis_tac[mem_cont_sim_trans] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (simp_tac (srw_ss()) [Abbr `t`, mstore_def, eval_operand_def] >>
      qpat_x_assum `eval_operand buf.buf_operand u = _` mp_tac >>
      simp_tac (srw_ss()) [eval_operand_def]) >>
  conj_tac >- metis_tac[not_fresh_at_def] >>
  conj_tac >- simp[Abbr `t`, mstore_def] >>
  conj_tac >- simp[Abbr `t`, mstore_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      simp_tac (srw_ss()) [Abbr `t`, mstore_def, eval_operand_def] >>
      qpat_x_assum `!op. _` (qspec_then `op` mp_tac) >>
      asm_rewrite_tac[] >> simp_tac (srw_ss()) [eval_operand_def]) >>
  drule window_phase_effect >> strip_tac >>
  metis_tac[abi_encoder_registered_effect_trans]
QED
Finalise custom_error_selector_prefix_run
