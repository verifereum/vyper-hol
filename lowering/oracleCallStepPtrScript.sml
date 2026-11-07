(* General CALL request checks.  Empty accesses require no site. *)
Theory oracleCallStepPtr
Ancestors
  bodyPtrDefs ptrSafeRun ptrDiscipline decoderGhostFramePtr contextCodegenRel codegenRel
  memLocDefs venomExecSemantics venomInst fragGasSeqPtr list pred_set finite_map
  venomCallOracleDefs venomCallOracleProps extCallOracle venomState

Theorem call_access_ok_ptr:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME an /\
  eval_operand ro s = SOME rw /\ eval_operand rz s = SOME rn /\
  (an <> 0w ==> ?p b sz. ao = Var p /\ FLOOKUP G p = SOME (b,sz) /\
                          b <= w2n aw /\ w2n aw + w2n an <= b + sz) /\
  (rn <> 0w ==> ?p b sz. ro = Var p /\ FLOOKUP G p = SOME (b,sz) /\
                          b <= w2n rw /\ w2n rw + w2n rn <= b + sz) ==>
  access_ok 0 G fn inst s
Proof
  strip_tac >>
  Cases_on `eval_operand gas s` >> Cases_on `eval_operand addr s` >>
  Cases_on `eval_operand value s` >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mem_read_ops_def, mem_write_ops_def,
       memory_range_of_operands_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[wordsTheory.w2n_eq_0]
QED

Theorem call_taint_ok_ptr:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN tn.t_mem) ==>
  taint_ok fn tn inst s
Proof
  strip_tac >> gvs[EVERY_MEM, taint_ok_def] >> metis_tac[]
QED

Theorem exec_ext_call_not_Halt:
  exec_ext_call inst s gas addr value ao az ro rz stat <> Halt t
Proof
  Cases_on `inst.inst_outputs` >> simp[exec_ext_call_def] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[exec_ext_call_def]
QED

Theorem call_step_not_Halt:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) ==>
  step_inst fuel ctx inst s <> Halt t
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def] >>
  simp[AllCaseEqs(), exec_ext_call_not_Halt] >>
  rpt strip_tac >> gvs[AllCaseEqs(), exec_ext_call_not_Halt]
QED

Theorem call_ptr_safe_step:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  access_ok 0 G fn inst s /\ taint_ok fn tn inst s /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s ==>
  ptr_safe_step (cx_dead cx) 0 fuel ctx fn PG G tn inst s
Proof
  strip_tac >> simp[Once ptr_safe_step_def, ptr_inst_ok_def] >>
  gvs[stor_taint_ok_def] >>
  metis_tac[call_step_not_Halt]
QED

Theorem call_adopted_stor_taint_ok:
  inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
  s'.vs_requests <> s.vs_requests /\ s'.vs_outcomes <> s.vs_outcomes /\
  (HD s.vs_outcomes).co_success /\ tn.t_imm = {} ==>
  stor_taint_ok cx (step_taint inst s s' tn) s'
Proof
  simp[stor_taint_ok_def, step_taint_def, adopt_reset_def, imm_taint_def]
QED

Theorem call_unchanged_stor_taint_ok:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  stor_taint_ok cx tn s /\
  s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient ==>
  stor_taint_ok cx (step_taint inst s s' tn) s'
Proof
  strip_tac >>
  gvs[stor_taint_ok_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def] >>
  metis_tac[SUBSET_EMPTY, EMPTY_SUBSET]
QED

Theorem call_gas_path_ptr_edge:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  access_ok 0 G fn inst s /\ taint_ok fn tn inst s /\
  allocas_from 0 s /\ ~ctx_has_dalloca ctx /\ stor_taint_ok cx tn s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK u ==>
  gas_path_ptr_edge (cx_dead cx) 0 ctx fn PG G tn s 0
    (step_prov PG G inst u) (step_taint inst s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_safe_step (cx_dead cx) 0 0 ctx fn PG G tn inst s` by
    (irule call_ptr_safe_step >> metis_tac[]) >>
  `ptr_inst_ok (cx_dead cx) 0 0 ctx fn G tn inst s` by
    gvs[Once ptr_safe_step_def] >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode` by
    simp[is_terminator_def] >>
  drule_all straight_line_ptr_edge >> simp[]
QED

Theorem call_written_bytes_clean:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  i IN range_bytes (step_writes inst s s') ==>
  i NOTIN (step_taint inst s s' tn).t_mem
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by simp[written_taint_def] >>
  drule step_taint_clean_write >> simp[DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED

Theorem call_step_exec_ext_call:
  ((~stat /\ inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (stat /\ inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME dw /\
  (~stat ==> eval_operand value s = SOME vw) /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME an /\
  eval_operand ro s = SOME rw /\ eval_operand rz s = SOME rn /\
  ~s.vs_call_ctx.cc_static ==>
  step_inst_base inst s =
  exec_ext_call inst s gw dw (if stat then 0w else vw) aw an rw rn stat
Proof
  strip_tac >> simp[step_inst_base_def]
QED

Theorem call_zero_access_ok_ptr:
  ((inst.inst_opcode = CALL /\
    inst.inst_operands = [gas; addr; value; ao; az; ro; rz]) \/
   (inst.inst_opcode = STATICCALL /\
    inst.inst_operands = [gas; addr; ao; az; ro; rz])) /\
  eval_operand ao s = SOME aw /\ eval_operand az s = SOME 0w /\
  eval_operand ro s = SOME rw /\ eval_operand rz s = SOME 0w ==>
  access_ok 0 G fn inst s
Proof
  strip_tac >> irule call_access_ok_ptr >> metis_tac[]
QED

Theorem consume_computed_call_storage_frame:
  computed_precompile rq /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient ==>
  (SND (consume_call_outcome rq ro rs s)).vs_accounts = s.vs_accounts /\
  (SND (consume_call_outcome rq ro rs s)).vs_transient = s.vs_transient
Proof
  strip_tac >> Cases_on `s.vs_outcomes` >>
  simp[consume_call_outcome_eq, take_outcome_def, adopt_outcome_def,
       failed_outcome_def] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> simp[] >>
  Cases_on `x` >> simp[] >>
  Cases_on `h.co_success` >> simp[adopt_outcome_def, failed_outcome_def]
QED

Theorem exec_ext_call_storage_cases:
  exec_ext_call inst s gas addr value ao az ro rz stat = OK u ==>
  u.vs_call_ctx = s.vs_call_ctx /\
  ((u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient) \/
   (~stat /\ ~s.vs_call_ctx.cc_static /\
    u.vs_requests <> s.vs_requests /\ u.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success))
Proof
  Cases_on `inst.inst_outputs` >> simp[exec_ext_call_def] >>
  rename1 `h::outs` >> Cases_on `outs` >> simp[exec_ext_call_def] >>
  strip_tac >> gvs[update_var_def] >>
  qmatch_goalsub_abbrev_tac `take_outcome rq s.vs_outcomes` >>
  Cases_on `computed_precompile rq`
  >- (`rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient` by
        simp[Abbr `rq`, venom_call_request_def] >>
      drule_all consume_computed_call_storage_frame >>
      simp[consume_call_outcome_eq]) >>
  `rq.cr_kind = MessageCall /\ rq.cr_accounts = s.vs_accounts /\
   rq.cr_tStorage = s.vs_transient /\
   rq.cr_static = (stat \/ s.vs_call_ctx.cc_static)` by
    simp[Abbr `rq`, venom_call_request_def] >>
  Cases_on `s.vs_outcomes` >>
  simp[take_outcome_def, adopt_outcome_def, failed_outcome_def] >>
  rename1 `s.vs_outcomes = outcome::rest` >>
  Cases_on `outcome.co_success` >>
  simp[adopt_outcome_def, record_request_def, Abbr `rq`, venom_call_request_def] >>
  Cases_on `stat` >> Cases_on `s.vs_call_ctx.cc_static` >> simp[]
QED

Theorem exec_ext_call_stor_taint_ok:
  ((inst.inst_opcode = CALL /\ ~stat) \/
   (inst.inst_opcode = STATICCALL /\ stat)) /\
  exec_ext_call inst s gas addr value ao az ro rz stat = OK u /\
  stor_taint_ok cx tn s ==>
  stor_taint_ok cx (step_taint inst s u tn) u
Proof
  strip_tac >> drule exec_ext_call_storage_cases >> strip_tac
  >- (irule call_unchanged_stor_taint_ok >> metis_tac[])
  >- (irule call_adopted_stor_taint_ok >> gvs[stor_taint_ok_def])
  >- (irule call_unchanged_stor_taint_ok >> metis_tac[]) >>
  gvs[]
QED
