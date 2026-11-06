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
  simp[] >> rpt strip_tac >> qexistsl_tac [`v`, `u`, `H`, `un`] >> simp[]
QED
