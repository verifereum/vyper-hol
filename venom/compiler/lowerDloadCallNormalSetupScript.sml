Theory lowerDloadCallNormalSetup
Ancestors
  lowerDloadNormalData lowerDloadCallFrameSetup lowerDloadAllocation
  lowerDloadCoverageInvariant
  lowerDloadOwnership lowerDloadFrameFloor lowerDloadFrameRepresentation
  lowerDloadSharedState calleeTransport ptrDiscipline venomExecSemantics
  venomState finite_map list pred_set

Theorem ld_call_normal_setup_backward:
  lower_dload_function_supply a child = (callee,b) /\
  opaque_use_ok caller /\ MEM ci (fn_insts caller) /\
  ci.inst_opcode = INVOKE /\ decode_invoke ci = SOME (nm,ops) /\
  taint_ok caller tn ci s /\
  V = set (fn_ir_vars caller) /\ U = {v | v IN V /\ ~retpc_var caller v} /\
  ld_normal_data CS caller V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  sf = <|lf_fn := caller; lf_inst := ci; lf_state := s;
          lf_params := AP; lf_prov := AG; lf_tvar := tn.t_var; lf_local := L|> /\
  tf = <|lf_fn := target_caller; lf_inst := ci; lf_state := t;
          lf_params := BP; lf_prov := BH; lf_tvar := un.t_var; lf_local := H|> /\
  FINITE child_keys /\
  eval_operands ops t = SOME args /\ setup_callee callee args t = SOME cs ==>
  ?sargs ss.
    eval_operands ops s = SOME sargs /\ setup_callee child sargs s = SOME ss /\
    ld_normal_data CS child childV {v | v IN childV /\ ~retpc_var child v}
      lo E FEMPTY FEMPTY (MAP (ld_op_prov AG) ops) (MAP (ld_op_prov BH) ops)
      FEMPTY FEMPTY (tn with t_var := FEMPTY) (un with t_var := FEMPTY)
      ss cs (sf::astk) live child_keys (32 * SUM (MAP CARD (A::suspended)))
      {} (A::suspended) (tf::gstk) t.vs_alloca_next
Proof
  strip_tac >>
  drule ld_normal_data_frame >> strip_tac >>
  `ld_owned_vars {v | MEM v (fn_ir_vars caller) /\ ~retpc_var caller v}
     E AG BH tn un s t` by
    (fs[ld_frame_data_def] >> gvs[]) >>
  `ld_shared_state tn un s t` by metis_tac[ld_frame_data_shared] >>
  drule_all ld_call_frame_setup_backward >>
  disch_then (qspecl_then [`childV`,`{v | v IN childV /\ ~retpc_var child v}`] strip_assume_tac) >>
  qexistsl_tac [`sargs`,`ss`] >> asm_rewrite_tac [] >>
  `ld_alloc_account child_keys (d + 32 * CARD A) {} ss cs` by
    (irule ld_alloc_account_enter >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> metis_tac[ld_normal_data_geometry]) >>
  drule ld_normal_data_geometry >> strip_tac >>
  drule ld_normal_data_masks >> strip_tac >>
  drule ld_normal_data_memory >> disch_tac >>
  drule ld_normal_data_companions >> strip_tac >>
  `cs.vs_alloca_next = t.vs_alloca_next /\ ss.vs_alloca_next = s.vs_alloca_next /\
   cs.vs_allocas = FEMPTY /\ ss.vs_allocas = FEMPTY /\
   cs.vs_memory = t.vs_memory /\ ss.vs_memory = s.vs_memory` by
    (qpat_assum `setup_callee callee args t = _` mp_tac >>
     qpat_assum `setup_callee child sargs s = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]) >>
  `ld_frame_bound cs.vs_alloca_next FEMPTY (MAP (ld_op_prov BH) ops) FEMPTY` by
    (asm_rewrite_tac [] >> irule ld_frame_bound_call >> goal_assum (drule_at Any)) >>
  `ss.vs_gas_readings = cs.vs_gas_readings /\
   (!a. a <> ss.vs_call_ctx.cc_address ==>
     (ss.vs_accounts a).storage = (cs.vs_accounts a).storage) /\
   (!a. a <> ss.vs_call_ctx.cc_address ==> ss.vs_transient a = cs.vs_transient a)` by
    (qpat_assum `setup_callee callee args t = _` mp_tac >>
     qpat_assum `setup_callee child sargs s = _` mp_tac >>
     qpat_assum `s.vs_gas_readings = t.vs_gas_readings` mp_tac >>
     qpat_assum `!a. a <> s.vs_call_ctx.cc_address ==> (s.vs_accounts a).storage = _` mp_tac >>
     qpat_assum `!a. a <> s.vs_call_ctx.cc_address ==> s.vs_transient a = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[setup_callee_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `lo <= t.vs_alloca_next` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `(!a. read_memory a 1 ss = read_memory a 1 s) /\
   (!a. read_memory a 1 cs = read_memory a 1 t)` by simp[read_memory_def] >>
  `ld_alloc_account child_keys (32 * CARD A + 32 * SUM (MAP CARD suspended)) {} ss cs` by
    (qpat_x_assum `ld_alloc_account child_keys _ _ _ _` mp_tac >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_COMM]) >>
  `!site. ld_live ((<|lf_fn := caller; lf_inst := ci; lf_state := s;
       lf_params := AP; lf_prov := AG; lf_tvar := tn.t_var; lf_local := L|>)::astk)
       FEMPTY (MAP (ld_op_prov AG) ops) FEMPTY site <=>
     ld_live astk L AP AG site` by
    (irule ld_live_call_shape >> simp[]) >>
  rewrite_tac[ld_normal_data_def] >>
  asm_simp_tac (srw_ss()) [op_taint_def, ld_stack_bound_def, allocas_from_def,
    arithmeticTheory.LEFT_ADD_DISTRIB, arithmeticTheory.ADD_COMM,
    ld_live_call_shape] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (rpt strip_tac >>
     qpat_x_assum `!owner bs bt sz. _ ==> _ /\ _ /\ _ <= s.vs_alloca_next /\ _`
       drule_all >> simp[])]
QED
