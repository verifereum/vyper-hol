Theory bodyPtrIntCallScratch
Ancestors
  bodyPtrIntCallMaterialize allocationPtr fragGasSeqPtr fragExecPtr
  ghostPcTransportPtr instIdxIndep exprLoweringProps context compileEnv
  loweringStateRelDefs venomInst venomExecSemantics bodyPtrDefs venomState
  finite_map words list pred_set fragExec ptrDiscipline bodyPtrIntCallEntryContracts
  bodyPtrMakeArrayWordStore loweringHalt

Theorem intcall_scratch_alloca_ptr:
  FLOOKUP s.vs_allocas aid = NONE /\
  s.vs_alloca_next + n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  intcall_completed env ce G tn s /\ return_buf_ptr d ce G tn s /\
  stor_taint_ok cx tn s /\
  (!p sz name. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> q) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> q) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    p <> q /\ op_taint tn (Var p) = {}) ==>
  ?t H un.
    run_inst_seq [mk_inst aid ALLOCA [Lit (n2w n)] [q]] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst aid ALLOCA [Lit (n2w n)] [q]] (s with vs_inst_idx := k) H un) /\
    (!bb. ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX [mk_inst aid ALLOCA [Lit (n2w n)] [q]]
        (DROP s.vs_inst_idx bb.bb_instructions) ==>
      gas_path_ptr D 0 ctx fn PG G tn s 0 H un
        (OK (t with vs_inst_idx := s.vs_inst_idx + 1))) /\
    intcall_completed env ce H un t /\ return_buf_ptr d ce H un t /\
    stor_taint_ok cx un t /\
    (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> op_taint un (Var p) = {}) /\
    t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next + n /\
    (!p. p <> q ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint un (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `n < dimword (:256) /\ s.vs_alloca_next < dimword (:256)` by decide_tac >>
  qabbrev_tac `t = update_var q (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+ (aid,(s.vs_alloca_next,n));
              vs_alloca_next := s.vs_alloca_next + n|>)` >>
  `step_inst_base (mk_inst aid ALLOCA [Lit (n2w n)] [q]) s = OK t` by
    simp[Abbr `t`, step_alloca_fresh] >>
  qabbrev_tac `H = G |+ (q,(s.vs_alloca_next,n))` >>
  qabbrev_tac `un = tn with <|t_mem := tn.t_mem UNION
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + n};
    t_var := tn.t_var |+ (q,{})|>` >>
  `step_prov PG G (mk_inst aid ALLOCA [Lit (n2w n)] [q]) t = H /\
   step_taint (mk_inst aid ALLOCA [Lit (n2w n)] [q]) s t tn = un` by
    (drule_all fresh_alloca_ghost >> simp[Abbr `H`, Abbr `un`]) >>
  `!p. p <> q ==> lookup_var p t = lookup_var p s /\
    FLOOKUP H p = FLOOKUP G p /\ op_taint un (Var p) = op_taint tn (Var p)` by
    simp[Abbr `t`, Abbr `H`, Abbr `un`, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE, op_taint_def] >>
  qexistsl_tac [`t`,`H`,`un`] >>
  conj_asm1_tac >- simp[run_inst_seq_def] >>
  conj_asm1_tac >-
    (gen_tac >> gvs[inst_seq_ptr_def, ptr_inst_ok_alloca,
      step_inst_inst_idx_indep, exec_result_map_def, mk_inst_def, is_terminator_def]) >>
  conj_tac >- suspend "path" >>
  conj_tac >- suspend "completed" >>
  conj_tac >- suspend "return" >>
  gvs[Abbr `t`, Abbr `un`, update_var_def, stor_taint_ok_def] >> metis_tac[]
QED

Resume intcall_scratch_alloca_ptr[path]:
  rpt strip_tac >>
  qpat_assum `run_inst_seq _ _ = _`
    (mp_then (Pos last) mp_tac run_inst_seq_gas_path_ptr) >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >> simp[] >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> gvs[mk_inst_def]
QED
Resume intcall_scratch_alloca_ptr[completed]:
  simp[intcall_completed_def] >> rpt strip_tac >>
  qpat_x_assum `intcall_completed env ce G tn s` mp_tac >>
  simp[intcall_completed_def] >> disch_then drule >> strip_tac >>
  qexistsl_tac [`p`,`sz`] >> simp[] >>
  `p <> q` by metis_tac[] >>
  `op_taint un (Var p) = {}` by
    (fs[intcall_local_value_def, ptr_covers_def] >> metis_tac[]) >>
  irule intcall_local_value_transport >> simp[] >>
  qexistsl_tac [`G`,`s`,`tn`] >>
  simp[Abbr `t`, Abbr `un`, update_var_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED
Resume intcall_scratch_alloca_ptr[return]:
  Cases_on `d` >> simp[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Finalise intcall_scratch_alloca_ptr
