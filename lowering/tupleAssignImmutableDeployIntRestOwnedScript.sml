Theory tupleAssignImmutableDeployIntRestOwned
Ancestors
  tupleAssignImmutableDeployIntRestTransport
  tupleAssignImmutableDeployIntGasLift tupleAssignImmutableDeployIntMemoryOwned
  tupleAssignImmutableDeployIntRestore gasOutcome gasExemptCert gasSummary
  bodyIntCallSeams exprSimDefs loweringPosts vyperTyping vyperInterpreter
  intCallStep compileEnv loweringStateRelDefs
  vyperState venomExecSemantics venomState fragGasPath fragExec fragGasMode fragGasFocus


Theorem tuple_immutable_intcall_memory_rest_owned:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_outcome F (cx_tops cx) (ctx,callee) (intcall_callee_src cx name ss)
    (es1,entered) (\res ee r. F)
    (intcall_callee_exit func ce cx rtv 0 (SOME w) n t) /\
  stmt_state_rel ctx func ce cx before t /\ before.scopes = prev /\
  evaluate_type (get_tenv cx) (TupleT stys) = SOME rtv /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,sz) /\
  origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
  type_memory_bytes ce (TupleT stys) <= sz /\
  eval_operand p.ptr_operand t = SOME w /\ p.ptr_location = LocMemory /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved ce sa /\
  (!lname lb lsz. local_region ce prev t lname lb lsz ==>
    w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
  (!lname b lsz id off asz.
    local_region ce prev t lname b lsz /\
    FLOOKUP t.vs_allocas id = SOME (off,asz) /\ n <= id ==>
    regions_disjoint b lsz off asz) /\
  (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst ==>
    EVERY (not_local_ptr ce prev) inst.inst_outputs /\
    (!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x)) /\
  (!v ee ir cs'.
    intcall_callee_exit func ce cx rtv 0 (SOME w) n t (INL v) ee (IntRet ir cs') ==>
    value_has_type rtv v /\
    immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
    (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb t.vs_inst_idx = SOME inst ==>
      LENGTH inst.inst_outputs = LENGTH ir.iret_values)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (intcall_rest cx name mut ss prev rtv) (es1,t)
    (\res ee u. ?v.
      res = INL (Value v) /\ stmt_state_rel ctx func ce cx ee u /\
      ee.scopes = prev /\
      vv_holds ce cx (TupleT stys) (Value v)
        (LocatedValue (TupleT stys) p) ee u /\
      eval_operand p.ptr_operand u = SOME w /\ p.ptr_location = LocMemory /\
      FLOOKUP u.vs_allocas aid = SOME (w2n w,sz) /\
      origin.cs_next_id <= aid /\ aid < final.cs_next_id /\
      type_memory_bytes ce (TupleT stys) <= sz /\
      (!lname lb lsz. local_region ce prev u lname lb lsz ==>
        w2n w + sz <= lb \/ lb + lsz <= w2n w) /\
      ~u.vs_halted /\ u.vs_current_bb = t.vs_current_bb /\
      u.vs_inst_idx = SUC t.vs_inst_idx)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  irule tuple_immutable_intcall_rest_transport >>
  qexistsl [`callee`, `ce`, `entered`, `n`, `0`, `SOME w`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_assum (drule_then strip_assume_tac) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func ce cx
    (ee with <|gas_obs := []; scopes := before.scopes|>)
    (returned with vs_inst_idx := SUC t.vs_inst_idx)` by
    (drule tuple_immutable_intcall_return_restore_next >>
     disch_then drule >> disch_then drule >> disch_then drule >>
     disch_then drule >> simp[] >>
     impl_tac >- metis_tac[] >> simp[]) >>
  `!x. MEM x inst.inst_outputs ==> ~not_fresh_at sa x` by metis_tac[] >>
  `EVERY (not_local_ptr ce before.scopes) inst.inst_outputs` by metis_tac[] >>
  drule tuple_immutable_memory_return_owned >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  simp[] >> disch_then (qspecl_then [`before.scopes`, `sa`] mp_tac) >>
  impl_tac >- metis_tac[arithmeticTheory.ADD_COMM] >> strip_tac >>
  qexists `returned with vs_inst_idx := SUC t.vs_inst_idx` >>
  simp[gas_marked_path_def, gas_path_rules] >>
  simp[vv_holds_def, read_result_def, return_def, is_word_type_def,
       eval_operand_def, local_region_def, lookup_var_def] >>
  conj_tac
  >- (`(ee with <|scopes := before.scopes; gas_obs := []|>) =
        (ee with <|gas_obs := []; scopes := before.scopes|>)` by
        simp[evaluation_state_component_equality] >> metis_tac[]) >>
  gvs[local_region_def, lookup_var_def]
QED
