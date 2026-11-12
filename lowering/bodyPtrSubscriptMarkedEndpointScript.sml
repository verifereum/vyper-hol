Theory bodyPtrSubscriptMarkedEndpoint
Ancestors
  bodyPtrSubscriptMarkedCompose bodyPtrSubscriptCurrentRootCase
  bodyPtrSubscriptCurrentRootEndpoint exprSimSource exprSimHypsDefs
  gasSummaryComposePtr exprSimDefs vyperState vyperValueOperation
  vyperTyping e2eDefs list exprSendPtr exprLoweringProps
  emitHelperProps emitHelper compileEnv fragExec venomState context

Theorem marked_index_endpoint_invariant:
  expr_body_pre cenv cx env idx es /\
  gas_marked_exec_ptr D (ctx,func) PG
    (vyperState$bind (eval_expr cx idx) (\r. read_result cx r))
    (es,s0,G0,tn0) marks (INL v) raw G tn (OK t) ==>
  expr_sim_inv cenv cx env (raw with gas_obs := [])
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_marked_exec_ptr_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  `expr_body_pre cenv cx env idx
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
  qpat_x_assum `expr_body_pre _ _ _ _ es` kall_tac >>
  drule expr_body_pre_eval >>
  disch_then (qspecl_then [`INL v`, `raw with gas_obs := []`] mp_tac) >>
  simp[]
QED

Theorem dynamic_root_selection_rejected:
  lookup_scopes id es.scopes = SOME entry /\
  entry.type = ArrayTV tv (Dynamic cap) /\
  entry.value = ArrayV (DynArrayV vs) /\
  (i < 0 \/ LENGTH vs <= Num i) ==>
  select_result cx ty (PlaceR (MemoryPlace id []))
    (ValueSubscript (IntV i)) es =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),es)
Proof
  strip_tac >>
  simp[select_result_def, extend_place_def, place_type_value_def,
       read_place_def, get_scopes_def, lift_option_type_def, bind_def,
       return_def, subscripts_type_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def, ignore_bind_def, extend_memory_place_def,
       array_index_def, raise_def] >>
  Cases_on `0 <= i` >> gvs[oEL_THM, return_def, raise_def] >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  gvs[return_def, raise_def]
QED

Theorem dynamic_root_selection_rejection_not_exempt:
  ~unspecified_behaviour_exempt tops
    (RuntimeError "evaluate_subscripts array_index")
Proof
  simp[unspecified_behaviour_exempt_def]
QED

Theorem emitted_selector_assert_rejects_ptr:
  emit_void ASSERT [arg] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME 0w /\ op_taint tn arg = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (Abort Revert_abort (revert_state (set_returndata [] s)))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ASSERT [arg] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  drule_all assert_fail_path_ptr >> simp[]
QED
