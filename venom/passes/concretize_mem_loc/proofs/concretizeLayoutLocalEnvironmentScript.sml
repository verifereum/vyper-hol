Theory concretizeLayoutLocalEnvironment
Ancestors frameRelocationEnvironment frameRelocationBinding frameJointDemand
  concretizeLayoutLocalValues ptrDiscipline codegenRel finite_map

Theorem env_reader_no_writes[local]:
  (inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) ==>
  step_writes inst s post = []
Proof
  strip_tac >> simp[step_writes_def, source_memory_write_ranges_def]
QED

Theorem concretize_env_reader_local_complete:
  vs0.vs_allocas = FEMPTY /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  (inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) /\
  inst.inst_outputs = [v] /\ step_inst_base inst s = OK post /\
  relocation_env s t /\
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
    relocation_env post tpost
Proof
  strip_tac >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, env_reader_no_writes, range_bytes_def] >> metis_tac[]) >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_env_reader_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c)`, `PG`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `update_var v z (t with vs_gas_readings := rest)` >> simp[]
QED
