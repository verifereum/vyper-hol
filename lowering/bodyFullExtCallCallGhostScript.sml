(* Ghost transport for the adopting oracle CALL endpoint. *)
Theory bodyFullExtCallCallGhost
Ancestors
  bodyFullExtCallGhost bodyFullExtCallFrames bodyFullUnwrapSlotPost
  bodyPtrDefs ptrDiscipline venomState venomInst finite_map pred_set

Theorem extcall_call_storage_ghost:
  (inst.inst_opcode = CALL \/ inst.inst_opcode = STATICCALL) /\
  stor_taint_ok_at D tn s /\ u.vs_call_ctx = s.vs_call_ctx /\
  u.vs_immutables = s.vs_immutables /\
  (~(inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
      u.vs_requests <> s.vs_requests /\ u.vs_outcomes <> s.vs_outcomes /\
      (HD s.vs_outcomes).co_success) ==>
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient) ==>
  stor_taint_ok_at D (step_taint inst s u tn) u
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = CALL /\ ~s.vs_call_ctx.cc_static /\
    u.vs_requests <> s.vs_requests /\ u.vs_outcomes <> s.vs_outcomes /\
    (HD s.vs_outcomes).co_success` >>
  gvs[stor_taint_ok_at_def, step_taint_def, adopt_reset_def,
      store_taint_def, imm_taint_def] >> metis_tac[]
QED

Theorem extcall_request_window_ghost:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  valid_horizon cx st0 H ee.storage_trace /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand buf_op t = SOME ro /\
  z.vs_allocas = t.vs_allocas /\ z.vs_alloca_next = t.vs_alloca_next /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!j. j < w2n ro \/ w2n ro + MIN cap (LENGTH rd) <= j ==>
    (j IN tn'.t_mem <=> j IN tn.t_mem)) /\
  stor_taint_ok_at D tn' z ==>
  ghost_inv_at D lo d cenv cx ee G' tn' z
Proof
  strip_tac >>
  `local_ptrs_rel func cenv ee.scopes t` by
    (fs[exprSimExtCallCaseTheory.extcall_request_ready_def,
        exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >> metis_tac[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[ghost_inv_at_def] >>
  `lo <= w2n ro` by
    (fs[exprSimExtCallCaseTheory.extcall_request_ready_def, allocas_from_def] >>
     metis_tac[optionTheory.SOME_11]) >>
  irule unwrap_slot_copy_ghost_inv_at >>
  simp[allocas_from_def] >>
  conj_tac >- metis_tac[allocas_from_def] >>
  qexistsl_tac [`G`, `func`, `MIN cap (LENGTH rd)`, `t`, `sp`, `w2n ro`, `tn`] >>
  simp[] >> rpt conj_tac
  >- (fs[exprSimExtCallCaseTheory.extcall_request_ready_def,
         loweringStateRelDefsTheory.regions_disjoint_def] >> rpt strip_tac >>
      first_x_assum drule >> simp[arithmeticTheory.MIN_DEF] >> decide_tac)
  >- (rpt strip_tac >>
      `not_fresh_at sp x` by
        (fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
         metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >> metis_tac[])
  >- (rpt strip_tac >>
      `not_fresh_at sp x` by
        (fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
         metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >> metis_tac[])
  >- (rpt strip_tac >>
      irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
      gvs[listTheory.LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF])
  >> fs[exprSimExtCallCaseTheory.extcall_request_ready_def]
QED

Theorem extcall_call_invariant:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  valid_horizon cx st0 H ee.storage_trace /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ((inst.inst_opcode = CALL /\ inst.inst_operands =
      [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) \/
   (inst.inst_opcode = STATICCALL /\ inst.inst_operands =
      [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)])) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand gas_op t = SOME gw /\ eval_operand addr_op t = SOME dw /\
  eval_operand value_op t = SOME vw /\ eval_operand call_offset t = SOME aw /\
  eval_operand call_len t = SOME an /\ eval_operand buf_op t = SOME ro /\
  z.vs_allocas = t.vs_allocas /\ z.vs_fmp = t.vs_fmp /\
  z.vs_alloca_next = t.vs_alloca_next /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  z.vs_returndata = rd /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t) /\
  z.vs_call_ctx = t.vs_call_ctx /\ z.vs_immutables = t.vs_immutables /\
  (~(inst.inst_opcode = CALL /\ ~t.vs_call_ctx.cc_static /\
      z.vs_requests <> t.vs_requests /\ z.vs_outcomes <> t.vs_outcomes /\
      (HD t.vs_outcomes).co_success) ==>
    z.vs_accounts = t.vs_accounts /\ z.vs_transient = t.vs_transient) /\
  ee'.scopes = ee.scopes ==>
  ghost_inv_at D lo d cenv cx ee' (step_prov PG G inst z)
    (step_taint inst t z tn) z
Proof
  strip_tac >>
  `cap < dimword (:256)` by
    (fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >> decide_tac) >>
  drule_at (Pat `_.inst_outputs = _`) extcall_call_ghost_frame >>
  simp[] >> disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  simp[eval_operand_def] >> disch_then (drule_at (Pat `_.vs_allocas = _`)) >>
  simp[] >> disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  `stor_taint_ok_at D (step_taint inst t z tn) z` by
    (irule extcall_call_storage_ghost >> fs[ghost_inv_at_def] >> metis_tac[]) >>
  `ghost_inv_at D lo d cenv cx ee (step_prov PG G inst z)
     (step_taint inst t z tn) z` suffices_by (strip_tac >> gvs[ghost_inv_at_def] >> metis_tac[]) >>
  irule extcall_request_window_ghost >> simp[] >>
  goal_assum (drule_at (Pat `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`G`, `H`, `rd`, `ro`, `tn`] >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED
