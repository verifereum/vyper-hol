Theory concretizeLayoutLocalAffine
Ancestors concretizeLayoutLocalOffset frameRelocationAffineSteps
  frameRelocationArithmeticClassification frameResolvedOrigins
  frameRelocationCleanOperands frameRelocationOpaque frameRelocationScalarSteps
  frameRelocationGuardedValues ptrDiscipline frameOriginUpdates
  venomExecSemantics venomState venomInst finite_map list
  concretizeLayoutLocalValues concretizeLayoutReaderContext frameRelocationEnvironment
  frameRelocationCleanValueSteps frameRelocationMemory frameRelocationReachableSupport
  concretizeLayoutLoadProduction frameRelocationBinding frameJointDemand frameJointTrace
  frameJointTransition frameResolvedTrace frameJointTaint frameOriginReachable
  frameOriginHistory codegenRel frameRelocationLocal frameRelocationDemand

Theorem affine_classified_step[local]:
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  taint_ok fn tn inst s /\
  (!u. FLOOKUP rv u <> NONE ==> u IN fn_pv P fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [a;b] /\ inst.inst_outputs = [v] /\
  s.vs_labels = t.vs_labels /\
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  step_inst_base inst s = OK post ==>
  ?ro tpost. ro = (case resolved_op rv a of NONE => resolved_op rv b | SOME x => SOME x) /\
    step_inst_base inst t = OK tpost /\
    local_rel (\u. F) (guarded_ptr (retpc_var fn) L (origin_set rv [v] ro))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] ro) (step_taint inst s post tn))
      R (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] ro)
Proof
  strip_tac >> (
  `!w. MEM (Var w) inst.inst_operands /\ FLOOKUP rv w = NONE ==>
       clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >>
     `~MEM inst.inst_opcode [ASSIGN; PHI; RET; MUL; SHL; SHR; SAR; MSTORE; SSTORE; TSTORE; ISTORE]` by simp[] >>
     drule_all disciplined_clean_scalar >> simp[]) >>
  `!w. MEM (Var w) inst.inst_operands ==> ~retpc_var fn w` by
    (rpt strip_tac >> drule_all disciplined_retpc_operand_use >> gvs[]) >>
  `!s t v x y. dead_result_rel D (Halt s) (Halt t) ==>
    dead_result_rel D (Halt (update_var v x s)) (Halt (update_var v y t))` by
    simp[dead_result_rel_def, update_var_def] >>
  Cases_on `resolved_op rv a`
  >- (Cases_on `resolved_op rv b`
      >- suspend "scalar"
      >> suspend "right") >>
  suspend "left")
QED

Resume affine_classified_step[scalar]:
  markerLib.RESUME_TAC >> (
  `!w. a = Var w \/ b = Var w ==> clean_scalar (retpc_var fn) rv tn w` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[resolved_op_def] >> metis_tac[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_scalar_binary_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  simp[scalar_binary_opcode_def] >>
  disch_then (qspec_then `PG` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[])
QED

Resume affine_classified_step[right]:
  markerLib.RESUME_TAC >> (
  Cases_on `b` >> gvs[resolved_op_def] >>
  rename1 `FLOOKUP rv w = SOME entry` >> PairCases_on `entry` >>
  `inst.inst_opcode = ADD` by
    (Cases_on `inst.inst_opcode = ADD` >> gvs[] >>
     drule_all resolved_sub_right_absent >> simp[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_scalar_add_pointer_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >> simp[] >>
  impl_tac >- (rpt strip_tac >> first_x_assum irule >> gvs[resolved_op_def] >> metis_tac[]) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[])
QED

Resume affine_classified_step[left]:
  markerLib.RESUME_TAC >> (
  Cases_on `a` >> gvs[resolved_op_def] >>
  rename1 `FLOOKUP rv w = SOME entry` >> PairCases_on `entry` >>
  `!u. b = Var u ==> FLOOKUP rv u = NONE` by
    (rpt strip_tac >> gvs[] >>
     Cases_on `inst.inst_opcode = ADD` >> gvs[] >>
     `FLOOKUP rv w <> NONE` by simp[] >>
     metis_tac[resolved_add_right_absent, resolved_sub_right_absent]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_pointer_binary_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >> simp[] >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[])
QED

Finalise affine_classified_step

Theorem affine_update_shape[local]:
  scalar_binary_opcode inst.inst_opcode /\ inst.inst_outputs = [v] /\
  step_inst_base inst s = OK post ==>
  ?a b z. inst.inst_operands = [a;b] /\ post = update_var v z s
Proof
  strip_tac >> drule scalar_binary_dispatch >> strip_tac >>
  `exec_pure2 f inst s = OK post` by metis_tac[] >>
  gvs[exec_pure2_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem concretize_affine_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_outputs = [v] /\ step_inst_base inst s = OK post /\
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
  ?a b ro tpost. inst.inst_operands = [a;b] /\
    ro = (case resolved_op rv a of NONE => resolved_op rv b | SOME x => SOME x) /\
    step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (origin_set rv [v] ro))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] ro)
        (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] ro) /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >> (
  `scalar_binary_opcode inst.inst_opcode` by simp[scalar_binary_opcode_def] >>
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
  drule_all affine_update_shape >> strip_tac >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) affine_classified_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  simp[] >> disch_then (qspecl_then [`PG`, `P`, `C`] mp_tac) >>
  simp[] >> strip_tac >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def] >> metis_tac[]) >>
  `?y. tpost = update_var v y t` by
    (drule_at (Pat `step_inst_base _ t = OK _`) affine_update_shape >> simp[] >> metis_tac[]) >>
  `step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})` by
    (gvs[] >> irule scalar_binary_taint >> simp[]) >>
  `step_taint inst t tpost un = un with t_var := un.t_var |+ (v,{})` by
    (gvs[] >> irule scalar_binary_taint >> simp[]) >>
  qexists_tac `tpost` >> gvs[] >>
  conj_tac
  >- (fs[local_rel_def] >> irule demand_agree_restrict >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule relocation_clean_write_taint >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> conj_tac
  >- (irule relocation_env_update_var >> simp[]) >>
  irule relocation_reader_context_update_var >> simp[])
QED

val _ = export_theory();
