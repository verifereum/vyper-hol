Theory bodyPtrIntCallScratch
Ancestors
  bodyPtrIntCallMaterialize allocationPtr fragGasSeqPtr fragExecPtr
  ghostPcTransportPtr instIdxIndep exprLoweringProps context compileEnv
  loweringStateRelDefs venomInst venomExecSemantics bodyPtrDefs venomState
  finite_map words list pred_set fragExec ptrDiscipline bodyPtrIntCallEntryContracts
  bodyPtrMakeArrayWordStore loweringHalt bodyPtrPrecompileBuiltinsAllocationFrame
  fragGasPathPtr

Theorem intcall_scratch_alloca_env_ptr:
  FLOOKUP s.vs_allocas aid = NONE /\
  s.vs_alloca_next + n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  intcall_completed env ce G tn s /\ return_buf_ptr d ce G tn s /\
  stor_taint_ok cx tn s /\
  (!p sz name entry. FLOOKUP env name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> p <> q) /\
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

Resume intcall_scratch_alloca_env_ptr[path]:
  rpt strip_tac >>
  qpat_assum `run_inst_seq _ _ = _`
    (mp_then (Pos last) mp_tac run_inst_seq_gas_path_ptr) >>
  simp[mk_inst_def, is_terminator_def] >> disch_then irule >> simp[] >>
  first_x_assum (qspec_then `s.vs_inst_idx` mp_tac) >> gvs[mk_inst_def]
QED
Resume intcall_scratch_alloca_env_ptr[completed]:
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
Resume intcall_scratch_alloca_env_ptr[return]:
  Cases_on `d` >> simp[return_buf_ptr_def] >>
  PairCases_on `x` >> gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Finalise intcall_scratch_alloca_env_ptr

(* The disabled branch is the optional, empty scratch tail. *)
Theorem intcall_scratch_path_word_env_ptr:
  (if enabled then compile_alloc_buffer n st else (buf,st)) = (buf,st') /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  (enabled ==> s.vs_alloca_next + w2n (n2w n : 256 word) < dimword (:256)) /\
  ~ctx_has_dalloca ctx /\
  intcall_completed env ce G tn s /\ return_buf_ptr d ce G tn s /\
  stor_taint_ok cx tn s /\
  (!p sz name entry. FLOOKUP env name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p /\ op_taint tn (Var p) = {}) ==>
  ?t H un.
    run_inst_seq (emitted_insts st st') s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
      (s with vs_inst_idx := k) H un) /\
    (!bb. ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
      gas_path_ptr D 0 ctx fn PG G tn s 0 H un
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')))) /\
    intcall_completed env ce H un t /\ return_buf_ptr d ce H un t /\
    stor_taint_ok cx un t /\
    (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> op_taint un (Var p) = {}) /\
    t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!p. not_fresh_at st p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint un (Var p) = op_taint tn (Var p))
Proof
  Cases_on `enabled` >> simp[] >> strip_tac
  >- (drule emitted_allocation_singleton >> strip_tac >>
      drule compile_alloc_buffer_parts >> strip_tac >>
      `FLOOKUP s.vs_allocas st.cs_next_id = NONE` by
        (simp[flookup_thm] >> metis_tac[prim_recTheory.LESS_REFL]) >>
      `!p. not_fresh_at st p ==> p <> STRING #"%" (toString st.cs_next_var)` by
        metis_tac[] >>
      `s.vs_alloca_next + w2n (n2w n : 256 word) < dimword (:256)` by simp[] >>
      `!p sz name entry. FLOOKUP env name = SOME entry /\
        FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
        p <> STRING #"%" (toString st.cs_next_var)` by metis_tac[] >>
      `!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==>
        p <> STRING #"%" (toString st.cs_next_var)` by metis_tac[] >>
      `!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
        p <> STRING #"%" (toString st.cs_next_var) /\ op_taint tn (Var p) = {}` by
        metis_tac[] >>
      drule_all (Q.INST [`n` |-> `w2n (n2w n : 256 word)`]
        intcall_scratch_alloca_env_ptr) >>
      simp[] >> disch_then (qspecl_then [`fn`,`PG`,`D`] mp_tac) >>
      strip_tac >> qexistsl_tac [`t`,`H`,`un`] >> simp[] >> metis_tac[]) >>
  gvs[] >> qexistsl_tac [`s`,`G`,`tn`] >>
  simp[emitted_insts_refl, run_inst_seq_def, inst_seq_ptr_def] >>
  rpt strip_tac >> simp[gas_path_ptr_rules]
QED

Theorem intcall_scratch_path_env_ptr:
  (if enabled then compile_alloc_buffer n st else (buf,st)) = (buf,st') /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  (enabled ==> s.vs_alloca_next + n < dimword (:256)) /\
  ~ctx_has_dalloca ctx /\
  intcall_completed env ce G tn s /\ return_buf_ptr d ce G tn s /\
  stor_taint_ok cx tn s /\
  (!p sz name entry. FLOOKUP env name = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p /\ op_taint tn (Var p) = {}) ==>
  ?t H un.
    run_inst_seq (emitted_insts st st') s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
      (s with vs_inst_idx := k) H un) /\
    (!bb. ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
      gas_path_ptr D 0 ctx fn PG G tn s 0 H un
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')))) /\
    intcall_completed env ce H un t /\ return_buf_ptr d ce H un t /\
    stor_taint_ok cx un t /\
    (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> op_taint un (Var p) = {}) /\
    t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!p. not_fresh_at st p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint un (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> irule intcall_scratch_path_word_env_ptr >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`buf`,`enabled`,`n`] >> simp[] >> strip_tac >>
  `n < dimword (:256)` by gvs[] >> simp[] >> gvs[]
QED

(* Compatibility contracts: the general proofs above only need env-backed locals. *)
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
  strip_tac >> irule intcall_scratch_alloca_env_ptr >> simp[] >> metis_tac[]
QED

Theorem intcall_scratch_path_ptr:
  (if enabled then compile_alloc_buffer n st else (buf,st)) = (buf,st') /\
  (!aid. aid IN FDOM s.vs_allocas ==> aid < st.cs_next_id) /\
  (enabled ==> s.vs_alloca_next + n < dimword (:256)) /\
  ~ctx_has_dalloca ctx /\
  intcall_completed env ce G tn s /\ return_buf_ptr d ce G tn s /\
  stor_taint_ok cx tn s /\
  (!p sz name. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==>
    not_fresh_at st p /\ op_taint tn (Var p) = {}) ==>
  ?t H un.
    run_inst_seq (emitted_insts st st') s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st')
      (s with vs_inst_idx := k) H un) /\
    (!bb. ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
      gas_path_ptr D 0 ctx fn PG G tn s 0 H un
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st')))) /\
    intcall_completed env ce H un t /\ return_buf_ptr d ce H un t /\
    stor_taint_ok cx un t /\
    (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> op_taint un (Var p) = {}) /\
    t.vs_memory = s.vs_memory /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_call_ctx = s.vs_call_ctx /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!p. not_fresh_at st p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint un (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> irule intcall_scratch_path_env_ptr >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`buf`,`enabled`,`n`] >> simp[] >> gvs[]
QED
