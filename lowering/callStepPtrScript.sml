Theory callStepPtr
Ancestors
  bodyPtrDefs ptrDiscipline venomCallOracleDefs vyperValue valueEncoding
  loweringPosts compileEnv exprLowering vyperAST extCallOracle
  ptrSafeRun contextCodegenRel codegenRel memLocDefs opcodeClass
  venomExecProofs venomExecSemantics venomState

(* The reset test is exposed without imposing restrictions on the old taint. *)
Theorem call_step_storage_taint:
  inst.inst_opcode = CALL ==>
  (step_taint inst s s' tn).t_stor =
    (if ~s.vs_call_ctx.cc_static /\
        s'.vs_requests <> s.vs_requests /\
        s'.vs_outcomes <> s.vs_outcomes /\
        (HD s.vs_outcomes).co_success then {} else tn.t_stor) /\
  (step_taint inst s s' tn).t_trans =
    (if ~s.vs_call_ctx.cc_static /\
        s'.vs_requests <> s.vs_requests /\
        s'.vs_outcomes <> s.vs_outcomes /\
        (HD s.vs_outcomes).co_success then {} else tn.t_trans)
Proof
  simp[step_taint_def, adopt_reset_def, store_taint_def]
QED

Theorem ptr_val_ok_none:
  ptr_val_ok cx NoneT NoneV (Lit 0w) G tn s
Proof
  simp[ptr_val_ok_def, ptr_mem_ok_def, op_taint_def, op_prov_def,
       evaluate_type_def, val_in_memory_def, val_footprint_def,
       type_memory_size_def]
QED

Theorem ptr_buf_ok_zero_type:
  type_memory_bytes cenv (lowered_value_type cenv e) = 0 ==>
  ptr_buf_ok cenv e op G s
Proof
  simp[ptr_buf_ok_def]
QED

Theorem send_none_buffer_size:
  type_memory_bytes cenv
    (lowered_value_type cenv (Call NoneT (Send has_gas) es ann)) = 0
Proof
  simp[lowered_value_type_def, expr_type_def, type_memory_bytes_def]
QED

Theorem consume_call_outcome_no_adoption:
  rq.cr_kind = MessageCall /\
  (rq.cr_static \/ ~(FST (take_outcome rq s.vs_outcomes)).co_success) ==>
  (SND (consume_call_outcome rq ro rz s)).vs_accounts = s.vs_accounts /\
  (SND (consume_call_outcome rq ro rz s)).vs_transient = s.vs_transient
Proof
  simp[consume_call_outcome_eq, adopt_outcome_def] >>
  strip_tac >> gvs[]
QED

Theorem consume_computed_call_accounts:
  computed_precompile rq /\ rq.cr_kind = MessageCall /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient ==>
  (SND (consume_call_outcome rq ro rz s)).vs_accounts = s.vs_accounts /\
  (SND (consume_call_outcome rq ro rz s)).vs_transient = s.vs_transient
Proof
  strip_tac >>
  simp[consume_call_outcome_eq, adopt_outcome_def] >>
  Cases_on `s.vs_outcomes` >> simp[take_outcome_def, failed_outcome_def] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> simp[] >>
  rename1 `precompile_result _ _ = SOME result` >>
  Cases_on `result` >> simp[failed_outcome_def] >>
  rename1 `s.vs_outcomes = outcome::rest` >>
  Cases_on `outcome.co_success` >> simp[failed_outcome_def]
QED

Theorem access_ok_call:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; rz] /\
  eval_operand gas s = SOME gw /\ eval_operand addr s = SOME aw /\
  eval_operand value s = SOME vw /\ eval_operand ao s = SOME aow /\
  eval_operand az s = SOME azw /\ eval_operand ro s = SOME row /\
  eval_operand rz s = SOME rzw /\
  (azw <> 0w ==> ?v b sz. ao = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                            b <= w2n aow /\ w2n aow + w2n azw <= b + sz) /\
  (rzw <> 0w ==> ?v b sz. ro = Var v /\ FLOOKUP G v = SOME (b,sz) /\
                            b <= w2n row /\ w2n row + w2n rzw <= b + sz) ==>
  access_ok lo G fn inst s
Proof
  strip_tac >>
  simp[access_ok_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, memory_range_of_operands_def,
       mem_read_ops_def, mem_write_ops_def] >>
  metis_tac[wordsTheory.w2n_eq_0]
QED

Theorem taint_ok_call:
  inst.inst_opcode = CALL /\
  EVERY (\op. op_taint tn op = {}) inst.inst_operands /\
  (!off len i. MEM (off,len) (source_memory_read_ranges inst s) /\
               off <= i /\ i < off + len ==> i NOTIN tn.t_mem) ==>
  taint_ok fn tn inst s
Proof
  simp[taint_ok_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem ptr_inst_ok_call:
  inst.inst_opcode = CALL /\ access_ok lo G fn inst s /\
  taint_ok fn tn inst s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) ==>
  ptr_inst_ok D lo fuel ctx fn G tn inst s
Proof
  strip_tac >> simp[ptr_inst_ok_def] >>
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  drule step_inst_base_halt_opcodes >> simp[]
QED

Theorem call_output_untainted:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; rz] /\
  inst.inst_outputs = [out] ==>
  op_taint (step_taint inst s s' tn) (Var out) = {} /\
  FLOOKUP (step_prov PG G inst s') out = NONE
Proof
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       step_prov_def, set_prov_def, out_prov_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem call_zero_region_memory_taint:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; Lit 0w] /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  (step_taint inst s s' tn).t_mem = tn.t_mem
Proof
  strip_tac >>
  simp[step_taint_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def,
       source_memory_write_ranges_def, eval_operand_def] >>
  Cases_on `eval_operand gas s` >> simp[range_bytes_def] >>
  Cases_on `eval_operand addr s` >> simp[range_bytes_def] >>
  Cases_on `eval_operand value s` >> simp[range_bytes_def] >>
  Cases_on `eval_operand ao s` >> simp[range_bytes_def] >>
  Cases_on `eval_operand az s` >> simp[range_bytes_def] >>
  Cases_on `eval_operand ro s` >> simp[range_bytes_def] >>
  simp[pred_setTheory.EXTENSION, finite_mapTheory.FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem call_old_variable_ghost:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\ x <> out ==>
  FLOOKUP (step_prov PG G inst s') x = FLOOKUP G x /\
  op_taint (step_taint inst s s' tn) (Var x) = op_taint tn (Var x)
Proof
  simp[step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, op_taint_def, set_var_taint_def,
       finite_mapTheory.FLOOKUP_DRESTRICT, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem call_ghost_kept:
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gas; addr; value; ao; az; ro; Lit 0w] /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sa out /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  ghost_kept cenv es sa G tn s (step_prov PG G inst s')
    (step_taint inst s s' tn)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> out` by metis_tac[] >>
  drule_all call_zero_region_memory_taint >> strip_tac >>
  simp[ghost_kept_def] >> rpt strip_tac >>
  `x <> out` by metis_tac[] >>
  drule_all call_old_variable_ghost >> simp[]
QED

Theorem call_stor_taint_ok:
  inst.inst_opcode = CALL /\ stor_taint_ok cx tn s /\
  s'.vs_call_ctx = s.vs_call_ctx /\
  (~(~s.vs_call_ctx.cc_static /\ s'.vs_requests <> s.vs_requests /\
      s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) ==>
   s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient) ==>
  stor_taint_ok cx (step_taint inst s s' tn) s'
Proof
  strip_tac >> drule call_step_storage_taint >> strip_tac >>
  gvs[stor_taint_ok_def] >>
  Cases_on `~s.vs_call_ctx.cc_static /\ s'.vs_requests <> s.vs_requests /\
            s'.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success` >>
  gvs[step_taint_def, imm_taint_def]
QED

Theorem call_ptr_covers:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\ p <> out /\
  lookup_var p s' = lookup_var p s ==>
  (ptr_covers (step_prov PG G inst s') (step_taint inst s s' tn) p s' sz <=>
   ptr_covers G tn p s sz)
Proof
  strip_tac >> drule_all call_old_variable_ghost >>
  simp[ptr_covers_def]
QED

Theorem call_ghost_inv:
  inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
  ghost_inv d cenv cx es G tn s /\ es'.scopes = es.scopes /\
  s'.vs_memory = s.vs_memory /\
  (step_taint inst s s' tn).t_mem = tn.t_mem /\
  (!p. p <> out ==> lookup_var p s' = lookup_var p s) /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> out) /\
  stor_taint_ok cx (step_taint inst s s' tn) s' ==>
  ghost_inv d cenv cx es' (step_prov PG G inst s')
    (step_taint inst s s' tn) s'
Proof
  strip_tac >>
  `!p sz. p <> out ==>
    (ptr_covers (step_prov PG G inst s') (step_taint inst s s' tn) p s' sz <=>
     ptr_covers G tn p s sz)` by
    (rpt strip_tac >> irule call_ptr_covers >> simp[]) >>
  gvs[ghost_inv_def] >>
  reverse (rpt conj_tac)
  >- metis_tac[call_old_variable_ghost]
  >- (Cases_on `d` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME pair) _ _ _ _` >>
      PairCases_on `pair` >> gvs[return_buf_ptr_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `p <> out` by metis_tac[] >>
  metis_tac[]
QED

Theorem consume_call_no_reset_accounts:
  rq = venom_call_request s aw vw ao az F /\
  t = SND (consume_call_outcome rq ro rz s) /\
  ~(~s.vs_call_ctx.cc_static /\ t.vs_requests <> s.vs_requests /\
    t.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success) ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient
Proof
  strip_tac >>
  Cases_on `computed_precompile rq`
  >- (drule consume_computed_call_accounts >>
      gvs[venom_call_request_def]) >>
  Cases_on `s.vs_outcomes` >>
  gvs[consume_call_outcome_eq, take_outcome_def, adopt_outcome_def,
      failed_outcome_def, record_request_def, venom_call_request_def] >>
  `s.vs_requests ++ [venom_call_request s aw vw ao az F] <> s.vs_requests` by
    (strip_tac >> pop_assum (mp_tac o AP_TERM ``LENGTH : call_request list -> num``) >>
     simp[]) >>
  `t' <> h::t'` by
    (strip_tac >> pop_assum (mp_tac o AP_TERM ``LENGTH : call_outcome list -> num``) >>
     simp[]) >> gvs[]
QED
