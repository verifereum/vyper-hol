Theory tupleAssignImmutableDeployIntStackRestOwned
Ancestors
  tupleAssignImmutableDeployIntRestTransport tupleAssignImmutableDeployIntRestore
  tupleAssignImmutableDeployIntStackOwned tupleAssignImmutableDeployInvokeOwned
  intCallFrame intCallStep exprSimCopy exprSimDefs loweringStateRelDefs
  bodyIntCallSeams gasOutcome compileEnv venomExecSemantics venomState
  fragGasPath fragGasMode list rich_list

Theorem tuple_immutable_intcall_stack_rest_owned_reachable:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name ss)
    (es1,entered) (\res ee r. F)
    (intcall_callee_exit func ce cx (TupleTV tvs) ret_count NONE n t) /\
  0 < ret_count /\
  stmt_state_rel ctx func ce cx before t /\ before.scopes = prev /\
  evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV tvs) /\
  EVERY (\etv. ?ty. is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME etv) tvs /\
  store_multi_results rbuf.buf_operand results 0 sa = ((),sb) /\
  local_ptrs_reserved ce sa /\
  (!x. rbuf.buf_operand = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce si /\
  eval_operand rbuf.buf_operand t = SOME w /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  (!lname lb lsz. local_region ce prev t lname lb lsz ==>
     w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  t.vs_current_bb = sa.cs_current_bb /\
  SUC t.vs_inst_idx = LENGTH sa.cs_current_insts /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  type_memory_bytes ce (TupleT stys) <= sz /\
  (!lname lb lsz. local_region ce prev t lname lb lsz ==>
     w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
  (!lname b lsz id off asz.
    local_region ce prev t lname b lsz /\
    FLOOKUP t.vs_allocas id = SOME (off,asz) /\ n <= id ==>
    regions_disjoint b lsz off asz) /\
  (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst ==>
    results = MAP Var inst.inst_outputs /\
    LENGTH inst.inst_outputs = ret_count /\ ALL_DISTINCT inst.inst_outputs /\
    EVERY (not_local_ptr ce prev) inst.inst_outputs /\
    (!x. MEM x inst.inst_outputs ==> not_fresh_at sa x) /\
    (!x. MEM x inst.inst_outputs ==> ~not_fresh_at si x) /\
    (!x. rbuf.buf_operand = Var x ==> ~MEM x inst.inst_outputs)) /\
  (!gs v ee ir cs'.
    intcall_callee_src cx name ss (es1 with gas_obs := gs) =
      (INL v,ee with gas_obs := []) /\
    intcall_callee_exit func ce cx (TupleTV tvs) ret_count NONE n t
      (INL v) (ee with gas_obs := []) (IntRet ir cs') ==>
    value_has_type (TupleTV tvs) v /\
    immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
    (ce.ce_is_ctor ==> !iname itv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,iname) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) iname = SOME (itv,iv) ==>
      regions_disjoint (w2n w) (32 * LENGTH results) off (type_memory_size itv))) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (intcall_rest cx name mut ss prev (TupleTV tvs)) (es1,t)
    (\res ee u. ?v.
      res = INL (Value v) /\ ee.scopes = prev /\
      stmt_state_rel ctx func ce cx ee u /\
      vv_holds ce cx (TupleT stys) (Value v)
        (LocatedValue (TupleT stys) (base_ptr rbuf)) ee u /\
      eval_operand rbuf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      type_memory_bytes ce (TupleT stys) <= sz /\
      (!lname lb lsz. local_region ce prev u lname lb lsz ==>
        w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  irule tuple_immutable_intcall_rest_transport_reachable >>
  qexistsl [`callee`, `ce`, `entered`, `n`, `ret_count`, `NONE`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_assum (drule_all_then strip_assume_tac) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `LENGTH ir.iret_values = ret_count` by gvs[intcall_callee_exit_def] >>
      metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func ce cx
    (ee with <|scopes := prev; gas_obs := []|>)
    (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (drule tuple_immutable_intcall_return_restore_next >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[] >>
     impl_tac >- (gvs[exprLoweringPropsTheory.immutable_alloca_sep_def] >> metis_tac[]) >> simp[]) >>
  `results = MAP Var inst.inst_outputs /\ ALL_DISTINCT inst.inst_outputs /\
   (!x. MEM x inst.inst_outputs ==> not_fresh_at sa x) /\
   (!x. MEM x inst.inst_outputs ==> ~not_fresh_at si x) /\
   (!x. rbuf.buf_operand = Var x ==> ~MEM x inst.inst_outputs)` by metis_tac[] >>
  drule_all bind_outputs_lookup >> strip_tac >>
  drule invoke_return_frame >> strip_tac >>
  `returned.vs_labels = t.vs_labels` by
    (Cases_on `ir.iret_adopt_fmp` >>
     gvs[adopt_return_fmp_def, merge_callee_state_def]) >>
  `eval_operand rbuf.buf_operand returned = SOME w` by
    (Cases_on `rbuf.buf_operand` >> gvs[eval_operand_def]) >>
  qpat_x_assum `returned = _ with vs_vars := _` kall_tac >>
  `MAP (\op. eval_operand op returned) results = MAP SOME ir.iret_values` by
    (simp[] >> irule LIST_EQ >> simp[EL_MAP, eval_operand_def]) >>
  `!x. not_fresh_at si x ==> lookup_var x returned = lookup_var x t` by metis_tac[] >>
  `!lname lb lsz. local_region ce prev returned lname lb lsz ==>
      local_region ce prev t lname lb lsz` by
    (rpt strip_tac >> drule_all copy_buffer_local_region_frame >> metis_tac[]) >>
  `intret_vals_match (TupleTV tvs) v ir.iret_values /\ ir.iret_values <> []` by
    (gvs[intcall_callee_exit_def, expr_exit_def] >> strip_tac >> gvs[]) >>
  `!lname lb lsz. local_region ce prev
      (returned with vs_inst_idx := SUC t.vs_inst_idx) lname lb lsz <=>
      local_region ce prev returned lname lb lsz` by
    simp[local_region_def, lookup_var_def] >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `s0` |-> `returned with vs_inst_idx := SUC t.vs_inst_idx`,
    `es` |-> `ee with <|scopes := prev; gas_obs := []|>`,
    `ws` |-> `ir.iret_values`] tuple_immutable_stack_return_owned_path) >>
  (impl_tac >- (simp[MEM_MAP, eval_operand_def, lookup_var_def] >>
                rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[])) >>
  qpat_assum `origin.cs_next_id <= aid` mp_tac >>
  qpat_assum `SUC t.vs_inst_idx = LENGTH sa.cs_current_insts` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> strip_tac >>
  disch_then (qx_choose_then `final` strip_assume_tac) >>
  qexists `final` >> simp[] >> gvs[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem tuple_immutable_intcall_stack_rest_owned:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name ss)
    (es1,entered) (\res ee r. F)
    (intcall_callee_exit func ce cx (TupleTV tvs) ret_count NONE n t) /\
  0 < ret_count /\
  stmt_state_rel ctx func ce cx before t /\ before.scopes = prev /\
  evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV tvs) /\
  EVERY (\etv. ?ty. is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME etv) tvs /\
  store_multi_results rbuf.buf_operand results 0 sa = ((),sb) /\
  local_ptrs_reserved ce sa /\
  (!x. rbuf.buf_operand = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce si /\
  eval_operand rbuf.buf_operand t = SOME w /\
  w2n w + 32 * LENGTH results < dimword (:256) /\
  (!lname lb lsz. local_region ce prev t lname lb lsz ==>
     w2n w + 32 * LENGTH results <= lb \/ lb + lsz <= w2n w) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  t.vs_current_bb = sa.cs_current_bb /\
  SUC t.vs_inst_idx = LENGTH sa.cs_current_insts /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < sa.cs_next_id /\
  type_memory_bytes ce (TupleT stys) <= sz /\
  (!lname lb lsz. local_region ce prev t lname lb lsz ==>
     w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
  (!lname b lsz id off asz.
    local_region ce prev t lname b lsz /\
    FLOOKUP t.vs_allocas id = SOME (off,asz) /\ n <= id ==>
    regions_disjoint b lsz off asz) /\
  (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst ==>
    results = MAP Var inst.inst_outputs /\
    LENGTH inst.inst_outputs = ret_count /\ ALL_DISTINCT inst.inst_outputs /\
    EVERY (not_local_ptr ce prev) inst.inst_outputs /\
    (!x. MEM x inst.inst_outputs ==> not_fresh_at sa x) /\
    (!x. MEM x inst.inst_outputs ==> ~not_fresh_at si x) /\
    (!x. rbuf.buf_operand = Var x ==> ~MEM x inst.inst_outputs)) /\
  (!v ee ir cs'.
    intcall_callee_exit func ce cx (TupleTV tvs) ret_count NONE n t
      (INL v) ee (IntRet ir cs') ==>
    value_has_type (TupleTV tvs) v /\
    immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
    (ce.ce_is_ctor ==> !iname itv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,iname) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) iname = SOME (itv,iv) ==>
      regions_disjoint (w2n w) (32 * LENGTH results) off (type_memory_size itv))) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (intcall_rest cx name mut ss prev (TupleTV tvs)) (es1,t)
    (\res ee u. ?v.
      res = INL (Value v) /\ ee.scopes = prev /\
      stmt_state_rel ctx func ce cx ee u /\
      vv_holds ce cx (TupleT stys) (Value v)
        (LocatedValue (TupleT stys) (base_ptr rbuf)) ee u /\
      eval_operand rbuf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      origin.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      type_memory_bytes ce (TupleT stys) <= sz /\
      (!lname lb lsz. local_region ce prev u lname lb lsz ==>
        w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> irule tuple_immutable_intcall_stack_rest_owned_reachable >>
  gvs[] >> conj_tac >- gvs[] >>
  conj_tac >- (qexists `before` >> simp[]) >>
  qexistsl [`callee`, `entered`, `n`, `results`, `ret_count`, `sa`, `si`] >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      first_assum (drule_then strip_assume_tac) >>
      gvs[exprLoweringPropsTheory.immutable_alloca_sep_def] >> metis_tac[]) >>
  metis_tac[]
QED
