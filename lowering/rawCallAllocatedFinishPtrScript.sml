(* Allocation-predecessor consumers of the checked finish branches. *)
Theory rawCallAllocatedFinishPtr
Ancestors
  rawCallFinishTotalPtr rawCallFinishAdaptersPtr callReadinessPtr
  rawCallOutcomeLengthPtr gasSummaryComposePtr rawCallAllocationProofPtr

(* The preservation clause is the one exported by outbuf_ready_stage.
   Keep the preallocation operands together instead of rebuilding their
   evaluation/provenance/taint facts separately in each finish branch. *)
Theorem raw_call_allocation_request_checks:
  EVERY (\arg. (!z. arg = Var z ==> not_fresh_at sa z) /\
    (!l. arg <> Label l) /\ op_taint tn arg = {})
    (if stat then [gas;addr;dp;dl] else [gas;addr;value;dp;dl]) /\
  (!arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) ==>
    eval_operand arg u = eval_operand arg s /\
    op_prov H arg = op_prov G arg /\ op_taint un arg = op_taint tn arg) /\
  eval_operand dp s = SOME (n2w (b+32)) /\
  eval_operand dl s = SOME (n2w (LENGTH bs)) /\
  op_prov G dp = SOME (region_base,sz) /\ region_base <= b /\
  b+32+LENGTH bs <= region_base+sz /\ b+32 < dimword(:256) /\
  LENGTH bs < dimword(:256) /\ cap < dimword(:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\ u.vs_memory = s.vs_memory /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN un.t_mem) /\
  eval_operand (Var rp) u = SOME ro /\ ptr_covers H un rp u cap ==>
  read_memory (w2n (n2w (b+32):bytes32))
    (w2n (n2w (LENGTH bs):bytes32)) u = bs /\
  (!iid outs.
    access_ok 0 H func (mk_inst iid (if stat then STATICCALL else CALL)
      (if stat then [gas;addr;dp;dl;Var rp;Lit (n2w cap)]
       else [gas;addr;value;dp;dl;Var rp;Lit (n2w cap)]) outs) u /\
    taint_ok func un (mk_inst iid (if stat then STATICCALL else CALL)
      (if stat then [gas;addr;dp;dl;Var rp;Lit (n2w cap)]
       else [gas;addr;value;dp;dl;Var rp;Lit (n2w cap)]) outs) u)
Proof
  strip_tac >>
  `EVERY (\arg. eval_operand arg u = eval_operand arg s /\
      op_prov H arg = op_prov G arg /\ op_taint un arg = {})
    (if stat then [gas;addr;dp;dl] else [gas;addr;value;dp;dl])` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `!arg. (!z. arg = Var z ==> _) /\ _ ==> _` kall_tac >>
  conj_tac >- (irule mem_bytes_at_read_memory_words >> gvs[]) >>
  rpt gen_tac >> conj_tac
  >- (irule (SRULE[] (GEN_ALL canonical_call_access_ok_ptr)) >>
      Cases_on `stat` >> fs[] >>
      simp[venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w] >>
      Cases_on `dp` >> gvs[ptrDisciplineTheory.op_prov_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  irule (SRULE[] (GEN_ALL canonical_call_taint_ok_ptr)) >>
  Cases_on `stat` >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_taint_def,
      venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w]
QED


Theorem raw_call_allocated_scalar_outcome:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) /\
  compile_raw_call_finish addr dp dl gas_op value_op
    (if flags.rcf_is_static then StaticCall else RegularCall) 0 F ov op sb = (result,sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) = SOME (BaseTV (BytesT (Dynamic lim))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword(:256) /\
  op_prov G dp = SOME (region_base,sz) /\ region_base <= b /\
  b+32+LENGTH bs <= region_base+sz /\ b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  EVERY (\arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) /\ op_taint tn arg = {})
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl]) /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~flags.rcf_is_static ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME (n2w (b+32)) /\ eval_operand dl s = SOME (n2w (LENGTH bs)) /\
  (~flags.rcf_is_static ==> w2n vw = amount) /\
  flags.rcf_max_outsize = 0 /\ ~flags.rcf_revert_on_failure /\ ~flags.rcf_is_delegate /\
  gas_admissible (eval_raw_call cx flags (w2w aw) bs amount source_gas) expr_vv_res_ok es ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags (w2w aw) bs amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v u J jn.
      res = INL (Value v) /\ ptr_val_ok cx (BaseT BoolT) v result H un t /\
      expr_val_rel cx (BaseT BoolT) v result t /\
      expr_val_at cenv cx (BaseT BoolT) sa sc ee v result t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G tn s J jn /\ wb_frame cenv es sa s u /\
      ghost_kept cenv es sa J jn u H un /\ wb_frame cenv es sa u t /\
      t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `(!z. dp = Var z ==> not_fresh_at sa z)` by (Cases_on `flags.rcf_is_static` >> fs[]) >>
  drule_all (SRULE[] (Q.INST [`cap` |-> `0`] raw_call_outbuf_ready_stage)) >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule_all raw_call_outbuf_finish_metadata >> strip_tac >>
  `dst = ob` by fs[wordsTheory.n2w_11] >> gvs[] >>
  `read_memory (b+32) (LENGTH bs) u = bs /\
    (!iid outs. access_ok 0 H func (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit 0w]) outs) u /\
      taint_ok func un (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit 0w]) outs) u)` by
    (irule (SRULE[] (Q.INST [`cap` |-> `0`] raw_call_allocation_request_checks)) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `(!aid a len. aid < sa.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint dst 0 a len)` by (metis_tac[raw_call_finish_alloca_separation]) >>
  `(!name a len. local_region cenv es.scopes u name a len ==> regions_disjoint dst 0 a len)` by
    (metis_tac[raw_call_finish_local_separation]) >>
  `EVERY (\arg. eval_operand arg u = eval_operand arg s)
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl])` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `allocas_from 0 u /\ stor_taint_ok cx un u` by
    fs[ptrDisciplineTheory.allocas_from_def, bodyPtrDefsTheory.ghost_inv_def] >>
  `eval_operand gas_op u = SOME gas /\ eval_operand addr u = SOME aw /\
    (~flags.rcf_is_static ==> eval_operand value_op u = SOME vw) /\
    eval_operand dp u = SOME (n2w (b+32)) /\ eval_operand dl u = SOME (n2w (LENGTH bs))` by
    (Cases_on `flags.rcf_is_static` >> gvs[]) >>
  drule_all raw_call_prepared_source_total >> strip_tac >>
  drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)
    (SRULE[compileEnvTheory.is_word_type_def] (Q.INST
      [`ty` |-> `BaseT BoolT`] raw_call_scalar_finish_outcome)) >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `ci_mono _ _`)) >>
  simp[] >> disch_then (qspecl_then [`vw`, `source_gas`, `PG`] mp_tac) >>
  impl_tac >- (Cases_on `flags.rcf_is_static` >> simp[] >> metis_tac[]) >>
  strip_tac >> irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexistsl_tac [`u`, `H`, `un`] >> gvs[] >>
  simp[loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
    compileEnvTheory.is_word_type_def, vyperValueTheory.evaluate_type_def,
    valueEncodingTheory.typed_val_to_w256_def]
QED

Theorem raw_call_allocated_zero_reverting_outcome:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) /\
  compile_raw_call_finish addr dp dl gas_op value_op
    (if flags.rcf_is_static then StaticCall else RegularCall) 0 T ov op sb = (result,sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) = SOME (BaseTV (BytesT (Dynamic lim))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword(:256) /\
  op_prov G dp = SOME (region_base,sz) /\ region_base <= b /\
  b+32+LENGTH bs <= region_base+sz /\ b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  EVERY (\arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) /\ op_taint tn arg = {})
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl]) /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~flags.rcf_is_static ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME (n2w (b+32)) /\ eval_operand dl s = SOME (n2w (LENGTH bs)) /\
  (~flags.rcf_is_static ==> w2n vw = amount) /\
  type_memory_bytes cenv (lowered_value_type cenv e) = 0 /\
  flags.rcf_max_outsize = 0 /\ flags.rcf_revert_on_failure /\ ~flags.rcf_is_delegate /\
  gas_admissible (eval_raw_call cx flags (w2w aw) bs amount source_gas) expr_vv_res_ok es ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags (w2w aw) bs amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v u J jn.
      res = INL (Value v) /\ ptr_val_ok cx NoneT v result H un t /\ ptr_buf_ok cenv e result H t /\
      expr_val_rel cx NoneT v result t /\
      expr_val_at cenv cx NoneT sa sc ee v result t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G tn s J jn /\ wb_frame cenv es sa s u /\
      ghost_kept cenv es sa J jn u H un /\ wb_frame cenv es sa u t /\
      t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `(!z. dp = Var z ==> not_fresh_at sa z)` by (Cases_on `flags.rcf_is_static` >> fs[]) >>
  drule_all (SRULE[] (Q.INST [`cap` |-> `0`] raw_call_outbuf_ready_stage)) >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule_all raw_call_outbuf_finish_metadata >> strip_tac >>
  `dst = ob` by fs[wordsTheory.n2w_11] >> gvs[] >>
  `read_memory (b+32) (LENGTH bs) u = bs /\
    (!iid outs. access_ok 0 H func (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit 0w]) outs) u /\
      taint_ok func un (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit 0w]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit 0w]) outs) u)` by
    (irule (SRULE[] (Q.INST [`cap` |-> `0`] raw_call_allocation_request_checks)) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `(!aid a len. aid < sa.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint dst 0 a len)` by (metis_tac[raw_call_finish_alloca_separation]) >>
  `(!name a len. local_region cenv es.scopes u name a len ==> regions_disjoint dst 0 a len)` by
    (metis_tac[raw_call_finish_local_separation]) >>
  `EVERY (\arg. eval_operand arg u = eval_operand arg s)
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl])` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `allocas_from 0 u /\ stor_taint_ok cx un u` by
    fs[ptrDisciplineTheory.allocas_from_def, bodyPtrDefsTheory.ghost_inv_def] >>
  `eval_operand gas_op u = SOME gas /\ eval_operand addr u = SOME aw /\
    (~flags.rcf_is_static ==> eval_operand value_op u = SOME vw) /\
    eval_operand dp u = SOME (n2w (b+32)) /\ eval_operand dl u = SOME (n2w (LENGTH bs))` by
    (Cases_on `flags.rcf_is_static` >> gvs[]) >>
  drule_all raw_call_prepared_source_total >> strip_tac >>
  `LENGTH outcome.co_returnData < dimword(:256)` by
    (irule take_call_outcome_returnData_length >> goal_assum (drule_at Any) >>
     fs[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  drule_at (Pat `ghost_inv _ _ _ _ _ _ _`) raw_call_zero_reverting_finish_outcome >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `ci_mono _ _`)) >>
  simp[] >> disch_then (qspecl_then [`vw`, `source_gas`, `e`, `PG`] mp_tac) >>
  impl_tac >- (Cases_on `flags.rcf_is_static` >> simp[] >> metis_tac[]) >>
  strip_tac >> irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexistsl_tac [`u`, `H`, `un`] >> gvs[] >>
  simp[loweringPostsTheory.expr_val_rel_def, loweringPostsTheory.expr_val_at_def,
    vyperValueTheory.evaluate_type_def, compileEnvTheory.is_word_type_def,
    venomStateTheory.eval_operand_def, valueEncodingDefsTheory.val_wf_def,
    valueEncodingDefsTheory.val_in_memory_def, loweringPostsTheory.val_footprint_def,
    valueEncodingTheory.type_memory_size_def]
QED

Theorem raw_call_allocated_positive_reverting_outcome:
  compile_raw_call_outbuf n sa = ((ov,op),sb) /\
  compile_raw_call_finish addr dp dl gas_op value_op
    (if flags.rcf_is_static then StaticCall else RegularCall) n T ov op sb = (result,sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) = SOME (BaseTV (BytesT (Dynamic lim))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword(:256) /\
  op_prov G dp = SOME (region_base,sz) /\ region_base <= b /\
  b+32+LENGTH bs <= region_base+sz /\ b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  EVERY (\arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) /\ op_taint tn arg = {})
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl]) /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~flags.rcf_is_static ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME (n2w (b+32)) /\ eval_operand dl s = SOME (n2w (LENGTH bs)) /\
  (~flags.rcf_is_static ==> w2n vw = amount) /\ 0 < n /\ n < dimword(:256) /\
  32+((n+31) DIV 32)*32 < dimword(:256) /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= 32+((n+31) DIV 32)*32 /\
  flags.rcf_max_outsize = n /\ flags.rcf_revert_on_failure /\ ~flags.rcf_is_delegate /\
  gas_admissible (eval_raw_call cx flags (w2w aw) bs amount source_gas) expr_vv_res_ok es ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags (w2w aw) bs amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v u J jn.
      res = INL (Value v) /\ ptr_val_ok cx (BaseT (BytesT (Dynamic n))) v result H un t /\
      expr_val_rel cx (BaseT (BytesT (Dynamic n))) v result t /\
      expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) sa sc ee v result t /\
      ptr_buf_ok cenv e result H t /\ stmt_state_rel ctx func cenv cx ee t /\
      ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G tn s J jn /\ wb_frame cenv es sa s u /\
      ghost_kept cenv es sa J jn u H un /\ wb_frame cenv es sa u t /\
      t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `(!z. dp = Var z ==> not_fresh_at sa z)` by (Cases_on `flags.rcf_is_static` >> fs[]) >>
  `(if n = 0 then 0 else ((n+31) DIV 32)*32+32) < dimword(:256)` by simp[] >>
  drule_all raw_call_outbuf_ready_stage >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule_all raw_call_outbuf_finish_metadata >> strip_tac >>
  `dst = ob+32` by (gvs[] >> fs[wordsTheory.n2w_11] >> decide_tac) >>
  qpat_x_assum `flags.rcf_max_outsize = n` mp_tac >> gvs[] >> disch_tac >>
  `read_memory (b+32) (LENGTH bs) u = bs /\
    (!iid outs. access_ok 0 H func (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit (n2w n)]) outs) u /\
      taint_ok func un (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit (n2w n)]) outs) u)` by
    (irule (SRULE[] raw_call_allocation_request_checks) >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `(!aid a len. aid < sa.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint ob (32+((n+31) DIV 32)*32) a len)` by (simp[] >> metis_tac[raw_call_finish_alloca_separation]) >>
  `(!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint ob (32+((n+31) DIV 32)*32) a len)` by (simp[] >> metis_tac[raw_call_finish_local_separation]) >>
  `EVERY (\arg. eval_operand arg u = eval_operand arg s)
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl])` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `allocas_from 0 u /\ stor_taint_ok cx un u` by fs[ptrDisciplineTheory.allocas_from_def, bodyPtrDefsTheory.ghost_inv_def] >>
  `eval_operand gas_op u = SOME gas /\ eval_operand addr u = SOME aw /\
    (~flags.rcf_is_static ==> eval_operand value_op u = SOME vw) /\
    eval_operand dp u = SOME (n2w (b+32)) /\ eval_operand dl u = SOME (n2w (LENGTH bs))` by
    (Cases_on `flags.rcf_is_static` >> gvs[]) >>
  drule_all raw_call_prepared_source_total >> strip_tac >>
  `LENGTH outcome.co_returnData < dimword(:256)` by
    (irule take_call_outcome_returnData_length >> goal_assum (drule_at Any) >> fs[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `n < dimword(:256)` by decide_tac >>
  drule_all raw_call_positive_bytes_finish_shape >>
  disch_then (qspec_then `outcome.co_returnData` assume_tac) >>
  drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)
    (Q.INST [`ty` |-> `BaseT (BytesT (Dynamic n))`] raw_call_positive_reverting_finish_outcome) >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[venomStateTheory.eval_operand_def] >> disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `ci_mono _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  simp[] >> disch_then (qspecl_then [`vw`, `source_gas`, `e`, `PG`] mp_tac) >>
  impl_tac >- (mp_tac (Q.INST [`cap` |-> `n`] raw_call_outbuf_capacity) >>
    Cases_on `flags.rcf_is_static` >> fs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  strip_tac >> irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexistsl_tac [`u`, `H`, `un`] >> gvs[] >>
  suspend "semantic"
QED

Resume raw_call_allocated_positive_reverting_outcome[semantic]:
  conj_tac
  >- (simp[loweringPostsTheory.expr_val_rel_def, venomStateTheory.eval_operand_def,
        compileEnvTheory.is_word_type_def] >>
      fs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
        compileEnvTheory.is_word_type_def, venomStateTheory.eval_operand_def] >>
      qpat_x_assum `!tv w. _ /\ lookup_var x t = SOME w ==> _` mp_tac >>
      simp[vyperValueTheory.evaluate_type_def] >> strip_tac >>
      first_x_assum (qspec_then `t.vs_memory` mp_tac) >>
      simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  simp[loweringPostsTheory.expr_val_at_def, vyperValueTheory.evaluate_type_def,
    compileEnvTheory.is_word_type_def] >>
  conj_tac
  >- (simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def] >>
      mp_tac (Q.SPEC `flags.rcf_max_outsize` valueTypingMemoryPropsTheory.word_size_capacity) >>
      simp[listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  simp[venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w] >>
  disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `ob`, `32 * ((flags.rcf_max_outsize+31) DIV 32)+32`] >>
  simp[loweringPostsTheory.val_footprint_def] >> conj_tac
  >- (`ci_mono sb sc` by
        (qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
         rpt (pop_assum kall_tac) >>
         metis_tac[exprLoweringPropsTheory.ci_mono_compile_raw_call_finish, pairTheory.SND]) >>
      fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def] >> decide_tac) >>
  conj_tac
  >- (mp_tac (Q.SPEC `flags.rcf_max_outsize` valueTypingMemoryPropsTheory.word_size_capacity) >>
      simp[listTheory.LENGTH_TAKE_EQ, vfmConstantsTheory.word_size_def] >> decide_tac) >>
  fs[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Finalise raw_call_allocated_positive_reverting_outcome

Theorem raw_call_allocated_positive_nonreverting_outcome:
  compile_raw_call_outbuf n sa = ((ov,op),sb) /\
  compile_raw_call_finish addr dp dl gas_op value_op
    (if flags.rcf_is_static then StaticCall else RegularCall) n F ov op sb = (result,sc) /\
  fn_has_code sa sb func /\ fn_has_code sb sc func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv dep cenv cx es G tn s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic lim))) sd sa es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) = SOME (BaseTV (BytesT (Dynamic lim))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword(:256) /\
  op_prov G dp = SOME (region_base,sz) /\ region_base <= b /\
  b+32+LENGTH bs <= region_base+sz /\ b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
  EVERY (\arg. (!z. arg = Var z ==> not_fresh_at sa z) /\ (!l. arg <> Label l) /\ op_taint tn arg = {})
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl]) /\
  eval_operand gas_op s = SOME gas /\ eval_operand addr s = SOME aw /\
  (~flags.rcf_is_static ==> eval_operand value_op s = SOME vw) /\
  eval_operand dp s = SOME (n2w (b+32)) /\ eval_operand dl s = SOME (n2w (LENGTH bs)) /\
  (~flags.rcf_is_static ==> w2n vw = amount) /\ 0 < n /\ n < dimword(:256) /\
  64+((n+31) DIV 32)*32 < dimword(:256) /\
  type_memory_bytes cenv (lowered_value_type cenv be) <= 32+((n+31) DIV 32)*32 /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= 64+((n+31) DIV 32)*32 /\
  flags.rcf_max_outsize = n /\ ~flags.rcf_revert_on_failure /\ ~flags.rcf_is_delegate /\
  gas_admissible (eval_raw_call cx flags (w2w aw) bs amount source_gas) expr_vv_res_ok es ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_raw_call cx flags (w2w aw) bs amount source_gas) (es,s,G,tn)
    (\res ee H un t. ?v u J jn.
      res = INL (Value v) /\
      ptr_val_ok cx (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) v result H un t /\
      expr_val_rel cx (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) v result t /\
      expr_val_at cenv cx (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]) sa sc ee v result t /\
      ptr_buf_ok cenv e result H t /\ stmt_state_rel ctx func cenv cx ee t /\
      ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G tn s J jn /\ wb_frame cenv es sa s u /\
      ghost_kept cenv es sa J jn u H un /\ wb_frame cenv es sa u t /\
      t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  `(!z. dp = Var z ==> not_fresh_at sa z)` by (Cases_on `flags.rcf_is_static` >> fs[]) >>
  `(if n = 0 then 0 else ((n+31) DIV 32)*32+32) < dimword(:256)` by simp[] >>
  drule_all raw_call_outbuf_ready_stage >> disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  drule_all raw_call_outbuf_finish_metadata >> strip_tac >>
  `dst = ob+32` by (gvs[] >> fs[wordsTheory.n2w_11] >> decide_tac) >>
  qpat_x_assum `flags.rcf_max_outsize = n` mp_tac >> gvs[] >> disch_tac >>
  `read_memory (b+32) (LENGTH bs) u = bs /\
    (!iid outs. access_ok 0 H func (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit (n2w n)]) outs) u /\
      taint_ok func un (mk_inst iid (if flags.rcf_is_static then STATICCALL else CALL)
      (if flags.rcf_is_static then [gas_op;addr;dp;dl;Var dx;Lit (n2w n)]
       else [gas_op;addr;value_op;dp;dl;Var dx;Lit (n2w n)]) outs) u)` by
    (irule (SRULE[] raw_call_allocation_request_checks) >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `(!aid a len. aid < sa.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (a,len) ==>
      regions_disjoint ob (32+((n+31) DIV 32)*32) a len)` by (simp[] >> metis_tac[raw_call_finish_alloca_separation]) >>
  `(!name a len. local_region cenv es.scopes u name a len ==>
      regions_disjoint ob (32+((n+31) DIV 32)*32) a len)` by (simp[] >> metis_tac[raw_call_finish_local_separation]) >>
  `EVERY (\arg. eval_operand arg u = eval_operand arg s)
    (if flags.rcf_is_static then [gas_op;addr;dp;dl] else [gas_op;addr;value_op;dp;dl])` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `allocas_from 0 u /\ stor_taint_ok cx un u` by fs[ptrDisciplineTheory.allocas_from_def, bodyPtrDefsTheory.ghost_inv_def] >>
  `eval_operand gas_op u = SOME gas /\ eval_operand addr u = SOME aw /\
    (~flags.rcf_is_static ==> eval_operand value_op u = SOME vw) /\
    eval_operand dp u = SOME (n2w (b+32)) /\ eval_operand dl u = SOME (n2w (LENGTH bs))` by
    (Cases_on `flags.rcf_is_static` >> gvs[]) >>
  drule_all raw_call_prepared_source_total >> strip_tac >>
  `LENGTH outcome.co_returnData < dimword(:256)` by
    (irule take_call_outcome_returnData_length >> goal_assum (drule_at Any) >> fs[exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `n < dimword(:256)` by decide_tac >>
  drule_all raw_call_positive_bytes_finish_shape >> disch_then (qspec_then `outcome.co_returnData` assume_tac) >>
  drule_all raw_call_positive_tuple_finish_shape >>
  disch_then (qspec_then `outcome.co_returnData` assume_tac) >>
  drule
    (Q.INST [`bty` |-> `BaseT (BytesT (Dynamic n))`,
      `ty` |-> `TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))]`] raw_call_positive_nonreverting_finish_outcome) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  simp[venomStateTheory.eval_operand_def] >> disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  simp[] >> disch_then (drule_at (Pat `ci_mono _ _`)) >>
  simp[] >> disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  simp[] >> disch_then (drule_at (Pat `type_memory_bytes _ _ <= _`)) >>
  simp[] >> disch_then (qspecl_then [`vw`, `source_gas`, `be`, `PG`] mp_tac) >>
  impl_tac >- (mp_tac (Q.INST [`cap` |-> `n`] raw_call_outbuf_capacity) >>
    Cases_on `flags.rcf_is_static` >> fs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  strip_tac >> irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >> qexistsl_tac [`u`, `H`, `un`] >> gvs[] >>
  suspend "semantic"
QED

Resume raw_call_allocated_positive_nonreverting_outcome[semantic]:
  conj_tac
  >- (simp[loweringPostsTheory.expr_val_rel_def] >>
      simp[compileEnvTheory.is_word_type_def] >>
      qpat_x_assum `ptr_val_ok _ (TupleT _) _ _ _ _ _` mp_tac >>
      simp[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
        compileEnvTheory.is_word_type_def] >>
      strip_tac >> qpat_x_assum `!mem. _ ==> val_in_memory _ _ _ mem`
        (qspec_then `t.vs_memory` mp_tac) >>
      simp[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  simp[loweringPostsTheory.expr_val_at_def, vyperValueTheory.evaluate_type_def,
    compileEnvTheory.is_word_type_def] >> conj_tac
  >- (simp[valueEncodingDefsTheory.val_wf_def, valueEncodingTheory.type_memory_size_def] >>
      mp_tac (Q.SPEC `flags.rcf_max_outsize` valueTypingMemoryPropsTheory.word_size_capacity) >>
      simp[listTheory.LENGTH_TAKE_EQ] >> decide_tac) >>
  `b' < dimword(:256)` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ ee t` mp_tac >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def] >> strip_tac >>
     `t.vs_alloca_next < dimword(:256)` by
       (irule exprLoweringPropsTheory.alloca_room_next_lt >> goal_assum (drule_at Any)) >>
     fs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP _ _ = SOME _ ==> _` drule >> decide_tac) >>
  simp[wordsTheory.w2n_n2w] >> disj1_tac >>
  qexistsl_tac [`ai`, `b'`, `32 * ((flags.rcf_max_outsize+31) DIV 32)+64`] >>
  simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
  fs[vfmConstantsTheory.word_size_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
  first_assum MATCH_ACCEPT_TAC
QED

Finalise raw_call_allocated_positive_nonreverting_outcome
