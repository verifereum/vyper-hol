Theory concretizeLayoutLocalExtcodeHash
Ancestors concretizeLayoutLocalExtcodeSize
  concretizeLayoutLocalIndexedContextReaders vfmState
  ptrDiscipline venomExecSemantics venomState frameRelocationEnvironment
  concretizeLayoutReaderContext frameRelocationGuardedValues codegenRel finite_map
  frameRelocationBinding frameJointDemand concretizeLayoutLocalValues
  concretizeLayoutOperandCleanliness frameRelocationCleanOperands
  frameRelocationReachableSupport frameJointTrace frameJointTransition
  frameResolvedTrace frameJointTaint frameOriginReachable frameOriginHistory
  pointerConfinedDefs memLocDefs frameRelocationCleanValueSteps
  frameRelocationLocal frameRelocationTaintOrder frameRelocationMemory

Theorem accounts_agree_except_empty:
  accounts_agree_except D a b ==>
  (account_empty (lookup_account addr a) <=> account_empty (lookup_account addr b))
Proof
  simp[accounts_agree_except_def, lookup_account_def] >> strip_tac >>
  first_x_assum (qspec_then `addr` mp_tac) >> strip_tac >>
  qpat_x_assum `_ with storage := _ = _`
    (mp_tac o AP_TERM ``account_empty``) >> simp[account_empty_def]
QED

Theorem extcodehash_execution:
  inst.inst_opcode = EXTCODEHASH /\ inst.inst_operands = [arg] /\
  inst.inst_outputs = [v] /\
  dead_result_rel D (Halt s) (Halt t) /\
  eval_operand arg s = eval_operand arg t /\
  step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\ step_inst_base inst t = OK (update_var v z t)
Proof
  strip_tac >>
  `!addr. (lookup_account addr s.vs_accounts).code =
           (lookup_account addr t.vs_accounts).code` by
    (rpt strip_tac >> irule accounts_agree_except_code >>
     qexists_tac `D` >> fs[dead_result_rel_def]) >>
  `!addr. account_empty (lookup_account addr s.vs_accounts) =
           account_empty (lookup_account addr t.vs_accounts)` by
    (rpt strip_tac >> irule accounts_agree_except_empty >>
     qexists_tac `D` >> fs[dead_result_rel_def]) >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_read1_def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  gvs[exec_read1_def] >> metis_tac[]
QED

Theorem extcodehash_ghosts:
  inst.inst_opcode = EXTCODEHASH /\ inst.inst_operands = [arg] /\
  inst.inst_outputs = [v] ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
  step_taint inst s (update_var v z s) tn = tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >> (conj_tac
  >- (simp[step_prov_def, out_prov_def, set_prov_def,
           frameOriginUpdatesTheory.origin_set_def, fmap_eq_flookup,
           FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
      gen_tac >> IF_CASES_TAC >> simp[])) >>
  `new_site_bytes s (update_var v z s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality] >>
  rpt CASE_TAC >> simp[]
QED

Theorem extcodehash_no_writes:
  inst.inst_opcode = EXTCODEHASH ==> step_writes inst s post = []
Proof
  simp[step_writes_def, source_memory_write_ranges_def]
QED

Theorem guarded_extcodehash_step:
  inst.inst_opcode = EXTCODEHASH /\ inst.inst_operands = [arg] /\
  inst.inst_outputs = [v] /\
  (!x. arg = Var x ==> clean_scalar Opaque rv tn x) /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) /\
  step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t) /\
    relocation_env post (update_var v z t) /\
    relocation_reader_context post (update_var v z t) /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE)
        (step_taint inst s post tn)) next
      (\s t. dead_result_rel D (Halt s) (Halt t))
      post (update_var v z t) /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le next (step_taint inst s post tn)
      (step_taint inst t (update_var v z t) un)
Proof
  strip_tac >>
  `eval_operand arg s = eval_operand arg t` by
    (drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_scalar_operand >>
     disch_then (qspec_then `arg` mp_tac) >>
     gvs[relocation_env_def] >> metis_tac[]) >>
  `dead_result_rel D (Halt s) (Halt t)` by
    (drule local_rel_observation >> simp[]) >>
  `?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t)` by
    (irule extcodehash_execution >> simp[] >> qexists_tac `D` >> simp[]) >>
  qexists_tac `z` >> simp[] >>
  `relocation_env post (update_var v z t)` by
    (gvs[] >> irule relocation_env_update_var >> simp[]) >>
  `relocation_reader_context post (update_var v z t)` by
    (gvs[] >> irule relocation_reader_context_update_var >> simp[]) >>
  `step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
   step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})` by
    (gvs[] >> metis_tac[extcodehash_ghosts]) >>
  `step_taint inst t (update_var v z t) un = un with t_var := un.t_var |+ (v,{})` by
    metis_tac[extcodehash_ghosts] >>
  gvs[] >> (conj_tac
  >- (simp[extcodehash_ghosts] >>
      irule guarded_clean_write_restrict >> simp[] >> metis_tac[])) >>
  simp[extcodehash_ghosts] >>
  irule relocation_clean_write_taint >> goal_assum (drule_at Any) >> simp[]
QED

Theorem concretize_extcodehash_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = EXTCODEHASH /\ inst.inst_operands = [arg] /\
  inst.inst_outputs = [v] /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  step_inst_base inst s = OK post /\
  relocation_env s t /\ relocation_reader_context s t /\
  local_rel (\u. F)
    (guarded_ptr (retpc_var fn)
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv)
    (guarded_bytes (retpc_var fn) rv tn)
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c)
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le
    (joint_relocation_demand lo (concretize_positions C') q0 es qs c) tn un ==>
  ?tpost. step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] NONE))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] NONE)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `frame_reachable vs0 C stk PG G tn fn inst s` by
    (drule_all joint_trace_edge_at >> strip_tac >> gvs[] >>
     fs[joint_config_reachable_def] >>
     metis_tac[joint_origin_history_erasure, origin_frame_erasure]) >>
  `taint_ok fn tn inst s` by
    (fs[ptr_discipline_def] >> metis_tac[]) >>
  `!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn` by
    (drule resolved_config_current >> simp[] >> strip_tac >>
     rpt strip_tac >> irule reachable_resolved_support >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `!x. arg = Var x ==> clean_scalar (retpc_var fn) rv tn x` by
    (rpt strip_tac >>
     `MEM (Var x) inst.inst_operands` by simp[] >>
     `~is_pointer_preserving_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
      ~MEM inst.inst_opcode [EQ; LT; GT; ASSIGN; PHI; RET; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE] /\
      mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
       simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
     drule_all nonpointer_operand_clean >> simp[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, extcodehash_no_writes, range_bytes_def] >> metis_tac[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_extcodehash_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c)`, `PG`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `update_var v z t` >> simp[]
QED

val _ = if null (hyp concretize_extcodehash_local_complete) then ()
        else raise Fail "extcodehash export has hypotheses";

val _ = export_theory();
