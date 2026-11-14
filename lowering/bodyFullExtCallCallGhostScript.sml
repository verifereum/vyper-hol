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

Theorem extcall_request_default_ghost:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  eval_operand buf_op t = SOME ro /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t /\
    FLOOKUP G' x = FLOOKUP G x) /\
  tn'.t_mem SUBSET tn.t_mem /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t) ==>
  !dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G' tn' z
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `safe_operand sp default_op /\
   extcall_default_ready cx ret_type has_default default_op default_ty default_opt t` by
    fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
  `?tv w. evaluate_type (get_tenv cx) default_ty = SOME tv /\
    val_wf tv dv /\ eval_operand default_op t = SOME w` by
    (fs[exprSimExtCallCaseTheory.extcall_default_ready_def] >> metis_tac[]) >>
  `eval_operand default_op z = eval_operand default_op t` by
    (Cases_on `default_op` >>
     fs[exprSafeOperandTheory.safe_operand_def, eval_operand_def] >> metis_tac[]) >>
  irule bodyPtrBopRepresentationFrameTheory.bop_ptr_mem_ok_frame >>
  qexistsl_tac [`G`, `t`, `tn`, `tv`] >> simp[] >>
  conj_tac >- (fs[exprSafeOperandTheory.safe_operand_def] >> metis_tac[]) >>
  rpt strip_tac
  >- (irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >>
      `LENGTH (TAKE cap rd) <= cap` by simp[listTheory.LENGTH_TAKE_EQ] >>
      fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
      `regions_disjoint (w2n ro) cap (w2n w) (val_footprint tv dv)` by metis_tac[] >>
      fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  fs[SUBSET_DEF]
QED

Theorem extcall_request_call_observations:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  eval_operand buf_op t = SOME ro /\
  tn'.t_mem = tn.t_mem DIFF {i | w2n ro <= i /\
    i < w2n ro + MIN cap (LENGTH rd)} /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    eval_operand buf_op t = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty /\
      type_memory_bytes cenv default_ty <> 0 ==>
    ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
      eval_operand default_op t = SOME w /\ b <= w2n w /\
      w2n w + type_memory_bytes cenv default_ty <= b + sz) ==>
  EVERY (\op. op_taint tn' op = {}) [addr_op; buf_op; default_op] /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G' v = SOME (b,sz) /\
    eval_operand buf_op z = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz /\
    (!i. w2n rw <= i /\ i < w2n rw + MIN cap (LENGTH rd) ==> i NOTIN tn'.t_mem)) /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty /\
      type_memory_bytes cenv default_ty <> 0 ==>
    ?x b sz w. default_op = Var x /\ FLOOKUP G' x = SOME (b,sz) /\
      eval_operand default_op z = SOME w /\ b <= w2n w /\
      w2n w + type_memory_bytes cenv default_ty <= b + sz)
Proof
  strip_tac >>
  `EVERY (safe_operand sp) [addr_op; buf_op; default_op]` by
    fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
  `!op. safe_operand sp op ==> eval_operand op z = eval_operand op t /\
    op_taint tn' op = op_taint tn op /\
    (!x. op = Var x ==> FLOOKUP G' x = FLOOKUP G x)` by
    (Cases >> fs[exprSafeOperandTheory.safe_operand_def, eval_operand_def,
                 op_taint_def] >> metis_tac[]) >>
  fs[listTheory.EVERY_DEF] >> conj_tac
  >- (strip_tac >> qpat_x_assum `cap <> 0 ==> _` drule >> strip_tac >>
      `rw = ro` by metis_tac[optionTheory.SOME_11] >>
      qexistsl_tac [`v`, `b`, `sz`] >> gvs[] >> metis_tac[]) >>
  metis_tac[]
QED


Theorem extcall_call_ghost_boundary:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  ((inst.inst_opcode = CALL /\ inst.inst_operands =
      [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) \/
   (inst.inst_opcode = STATICCALL /\ inst.inst_operands =
      [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)])) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand gas_op t = SOME gw /\ eval_operand addr_op t = SOME dw /\
  eval_operand value_op t = SOME vw /\ eval_operand call_offset t = SOME aw /\
  eval_operand call_len t = SOME an /\ eval_operand buf_op t = SOME ro /\
  z.vs_allocas = t.vs_allocas /\ z.vs_fmp = t.vs_fmp /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  z.vs_returndata = rd /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        eval_operand default_op t = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    eval_operand buf_op t = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz) ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 (step_prov PG G inst z) (step_taint inst t z tn) /\
  EVERY (\op. op_taint (step_taint inst t z tn) op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op (step_prov PG G inst z)
      (step_taint inst t z tn) z /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP (step_prov PG G inst z) x = SOME (b,sz) /\
        eval_operand default_op z = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\
    FLOOKUP (step_prov PG G inst z) v = SOME (b,sz) /\
    eval_operand buf_op z = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz /\
    (!i. w2n rw <= i /\ i < w2n rw + MIN cap (LENGTH rd) ==>
      i NOTIN (step_taint inst t z tn).t_mem))
Proof
  strip_tac >>
  `cap < dimword (:256) /\ sa.cs_next_var <= sp.cs_next_var` by
    (fs[exprSimExtCallCaseTheory.extcall_request_ready_def] >> decide_tac) >>
  drule_at (Pat `_.inst_outputs = _`) extcall_call_ghost_frame >>
  simp[] >> disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  simp[eval_operand_def] >> disch_then (drule_at (Pat `_.vs_allocas = _`)) >>
  simp[] >> disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  `!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t /\
    FLOOKUP (step_prov PG G inst z) x = FLOOKUP G x /\
    op_taint (step_taint inst t z tn) (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  `!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op (step_prov PG G inst z)
      (step_taint inst t z tn) z` by
    (drule extcall_request_default_ghost >>
     disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `_.vs_memory = _`)) >>
     disch_then (drule_at (Pat `_.t_mem SUBSET _.t_mem`)) >>
     disch_then (qspecl_then [`step_prov PG G inst z`, `G`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  `EVERY (\op. op_taint (step_taint inst t z tn) op = {})
      [addr_op; buf_op; default_op] /\
   (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\
     FLOOKUP (step_prov PG G inst z) v = SOME (b,sz) /\
     eval_operand buf_op z = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz /\
     (!i. w2n rw <= i /\ i < w2n rw + MIN cap (LENGTH rd) ==>
       i NOTIN (step_taint inst t z tn).t_mem)) /\
   (!dv. default_opt = SOME dv /\ ~is_word_type default_ty /\
       type_memory_bytes cenv default_ty <> 0 ==>
     ?x b sz w. default_op = Var x /\
       FLOOKUP (step_prov PG G inst z) x = SOME (b,sz) /\
       eval_operand default_op z = SOME w /\ b <= w2n w /\
       w2n w + type_memory_bytes cenv default_ty <= b + sz)` by
    (irule extcall_request_call_observations >>
     goal_assum (drule_at (Pat `extcall_request_ready _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     qexistsl_tac [`G`, `ro`, `tn`] >>
     simp[] >> metis_tac[]) >>
  `~not_fresh_at sa out` by
    (strip_tac >> drule_all loweringShapeDefsTheory.not_fresh_at_mono >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `step_prov _ _ _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
      first_assum irule >> simp[]) >>
  gvs[listTheory.EVERY_DEF] >> metis_tac[]
QED

Theorem extcall_ghost_inv_next_inst:
  ghost_inv_at D lo d cenv cx ee G tn (next_inst t) <=>
  ghost_inv_at D lo d cenv cx ee G tn t
Proof
  simp[ghost_inv_at_def, next_inst_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def] >>
  PairCases_on `x` >> simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

Theorem extcall_call_ghost_kept:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  ((inst.inst_opcode = CALL /\ inst.inst_operands =
      [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) \/
   (inst.inst_opcode = STATICCALL /\ inst.inst_operands =
      [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)])) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand gas_op t = SOME gw /\ eval_operand addr_op t = SOME dw /\
  eval_operand value_op t = SOME vw /\ eval_operand call_offset t = SOME aw /\
  eval_operand call_len t = SOME an /\ eval_operand buf_op t = SOME ro /\
  z.vs_allocas = t.vs_allocas /\ z.vs_fmp = t.vs_fmp /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  z.vs_returndata = rd /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        eval_operand default_op t = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    eval_operand buf_op t = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz) ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 (step_prov PG G inst z) (step_taint inst t z tn)
Proof
  MATCH_ACCEPT_TAC (cj 1 extcall_call_ghost_boundary)
QED

Theorem extcall_call_ghost_operands:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  ((inst.inst_opcode = CALL /\ inst.inst_operands =
      [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) \/
   (inst.inst_opcode = STATICCALL /\ inst.inst_operands =
      [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)])) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand gas_op t = SOME gw /\ eval_operand addr_op t = SOME dw /\
  eval_operand value_op t = SOME vw /\ eval_operand call_offset t = SOME aw /\
  eval_operand call_len t = SOME an /\ eval_operand buf_op t = SOME ro /\
  z.vs_allocas = t.vs_allocas /\ z.vs_fmp = t.vs_fmp /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  z.vs_returndata = rd /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        eval_operand default_op t = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    eval_operand buf_op t = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz) ==>
  EVERY (\op. op_taint (step_taint inst t z tn) op = {}) [addr_op; buf_op; default_op]
Proof
  MATCH_ACCEPT_TAC (cj 2 extcall_call_ghost_boundary)
QED

Theorem extcall_call_ghost_default:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  ((inst.inst_opcode = CALL /\ inst.inst_operands =
      [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) \/
   (inst.inst_opcode = STATICCALL /\ inst.inst_operands =
      [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)])) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand gas_op t = SOME gw /\ eval_operand addr_op t = SOME dw /\
  eval_operand value_op t = SOME vw /\ eval_operand call_offset t = SOME aw /\
  eval_operand call_len t = SOME an /\ eval_operand buf_op t = SOME ro /\
  z.vs_allocas = t.vs_allocas /\ z.vs_fmp = t.vs_fmp /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  z.vs_returndata = rd /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        eval_operand default_op t = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    eval_operand buf_op t = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz) ==>
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op (step_prov PG G inst z)
      (step_taint inst t z tn) z /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP (step_prov PG G inst z) x = SOME (b,sz) /\
        eval_operand default_op z = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz))
Proof
  MATCH_ACCEPT_TAC (cj 3 extcall_call_ghost_boundary)
QED

Theorem extcall_call_ghost_buffer:
  extcall_request_ready st0 ctx func cenv cx ret_type es sa s0 sp stat
    addr_op value_op gas_op buf_op call_offset call_len cap target value_opt
    calldata has_default default_op default_ty default_opt ee t /\
  ((inst.inst_opcode = CALL /\ inst.inst_operands =
      [gas_op; addr_op; value_op; call_offset; call_len; buf_op; Lit (n2w cap)]) \/
   (inst.inst_opcode = STATICCALL /\ inst.inst_operands =
      [gas_op; addr_op; call_offset; call_len; buf_op; Lit (n2w cap)])) /\
  inst.inst_outputs = [out] /\ ~not_fresh_at sp out /\
  eval_operand gas_op t = SOME gw /\ eval_operand addr_op t = SOME dw /\
  eval_operand value_op t = SOME vw /\ eval_operand call_offset t = SOME aw /\
  eval_operand call_len t = SOME an /\ eval_operand buf_op t = SOME ro /\
  z.vs_allocas = t.vs_allocas /\ z.vs_fmp = t.vs_fmp /\
  z.vs_memory = (write_memory_with_expansion (w2n ro) (TAKE cap rd) t).vs_memory /\
  z.vs_returndata = rd /\
  (!x. not_fresh_at sp x ==> lookup_var x z = lookup_var x t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. op_taint tn op = {}) [addr_op; buf_op; default_op] /\
  (!dv. default_opt = SOME dv /\ ~is_word_type default_ty ==>
    ptr_mem_ok cx default_ty dv default_op G tn t /\
    (type_memory_bytes cenv default_ty <> 0 ==>
      ?x b sz w. default_op = Var x /\ FLOOKUP G x = SOME (b,sz) /\
        eval_operand default_op t = SOME w /\ b <= w2n w /\
        w2n w + type_memory_bytes cenv default_ty <= b + sz)) /\
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\ FLOOKUP G v = SOME (b,sz) /\
    eval_operand buf_op t = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz) ==>
  (cap <> 0 ==> ?v b sz rw. buf_op = Var v /\
    FLOOKUP (step_prov PG G inst z) v = SOME (b,sz) /\
    eval_operand buf_op z = SOME rw /\ b <= w2n rw /\ w2n rw + cap <= b + sz /\
    (!i. w2n rw <= i /\ i < w2n rw + MIN cap (LENGTH rd) ==>
      i NOTIN (step_taint inst t z tn).t_mem))
Proof
  MATCH_ACCEPT_TAC (cj 4 extcall_call_ghost_boundary)
QED

val _ = List.app (fn th => if null (hyp th) then () else raise Fail "open call ghost export")
  [extcall_request_call_observations, extcall_call_ghost_boundary,
   extcall_call_ghost_kept, extcall_call_ghost_operands,
   extcall_call_ghost_default, extcall_call_ghost_buffer];
