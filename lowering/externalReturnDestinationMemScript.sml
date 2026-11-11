(* The actual destination ALLOCA, including repeated execution of a site. *)
Theory externalReturnDestinationMem
Ancestors
  externalReturnNormalizeRun actualAllocExec allocaSiteResource memContinuation
  loweringHalt exprLoweringProps localPtrsProps compileEnv context
  venomExecSemantics venomState venomInst finite_map words

Theorem return_destination_alloc_mem_cont:
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
    s.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ u.vs_call_ctx = s.vs_call_ctx /\
    u.vs_data_section = s.vs_data_section /\
    (!op. (!x. op = Var x ==> not_fresh_at st x) ==>
      eval_operand op u = eval_operand op s) /\
    (!id p sz. FLOOKUP s.vs_allocas id = SOME (p,sz) ==>
      FLOOKUP u.vs_allocas id = SOME (p,sz)) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP u.vs_allocas id = FLOOKUP s.vs_allocas id)
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
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `inst`]) >>
  drule_all normalize_alloc_mem_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH en.cs_current_insts`, `b`] >>
  simp_tac (srw_ss()) [] >>
  suspend "endpoint"
QED

Resume return_destination_alloc_mem_cont[endpoint]:
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `~(_ with vs_inst_idx := _).vs_halted` mp_tac >>
    simp_tac (srw_ss()) []) >>
  conj_tac >- (qpat_x_assum `(_ with vs_inst_idx := _).vs_current_bb = _` mp_tac >>
    simp_tac (srw_ss()) []) >>
  conj_tac
  >- (qpat_x_assum `lookup_var _ t = _` mp_tac >>
      qpat_x_assum `buf.buf_operand = _` mp_tac >>
      rpt (pop_assum kall_tac) >> simp[eval_operand_def]) >>
  conj_tac >- (qpat_x_assum `buf.buf_operand = _` SUBST1_TAC >>
    simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_x_assum `FLOOKUP t.vs_allocas inst.inst_id = _` mp_tac >>
    qpat_x_assum `inst.inst_id = _` mp_tac >>
    qpat_x_assum `n < _` mp_tac >> rpt (pop_assum kall_tac) >> simp[]) >>
  conj_tac >- (qpat_x_assum `b + _ <= _` mp_tac >>
    qpat_x_assum `n < _` mp_tac >> rpt (pop_assum kall_tac) >> simp[]) >>
  conj_tac
  >- (drule alloca_room_next_lt >>
      metis_tac[w2n_n2w, arithmeticTheory.LESS_MOD,
        arithmeticTheory.LESS_EQ_LESS_TRANS]) >>
  conj_tac
  >- (irule alloca_room_fields >> qexists_tac `t` >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >>
      `op <> Var (STRING #"%" (toString st.cs_next_var))` by metis_tac[] >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `exec_alloca inst _ _ = _` mp_tac >>
  qpat_x_assum `inst.inst_id = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp[exec_alloca_def] >> rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE]
QED

Finalise return_destination_alloc_mem_cont
