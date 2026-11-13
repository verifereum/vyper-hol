Theory concretizeLayoutCallSetupMemory
Ancestors frameRelocationBinding frameJointDemand frameRelocationLocal frameRelocationTaintOrder
  frameRelocationDemand frameRelocationCopyTaint frameRelocationValues calleeTransport venomExecProps
  venomExecSemantics venomState ptrDiscipline finite_map pred_set list

(* NONE pushes a frame but performs no write. Demand restriction does not
   identify the two activation caches or the two relocation relations. *)
Theorem layout_call_demand_retained:
  joint_trace vs0 C q0 es qs q /\ vs0.vs_allocas = FEMPTY /\
  n < LENGTH es /\ EL n es = NONE /\
  joint_relocation_demand lo positions q0 es qs (SUC n) a z ==>
  joint_relocation_demand lo positions q0 es qs n a z
Proof
  strip_tac >>
  `a NOTIN joint_writes (EL n (q0::qs)) (EL n es)` by simp[joint_writes_call] >>
  drule_all joint_relocation_demand_retained >> simp[]
QED

Theorem layout_setup_demand_agree:
  demand_agree R (\a. read_byte a s.vs_memory) (\b. read_byte b t.vs_memory) /\
  (!a b. next a b ==> R a b) /\
  setup_callee fn args s = SOME cs /\ setup_callee gn args' t = SOME ct ==>
  demand_agree next (\a. read_byte a cs.vs_memory) (\b. read_byte b ct.vs_memory)
Proof
  strip_tac >> dxrule setup_callee_shared_fields >> strip_tac >>
  drule setup_callee_shared_fields >> strip_tac >>
  gvs[] >> irule demand_agree_restrict >> goal_assum (drule_at Any) >> simp[]
QED

Theorem layout_call_taint_restrict:
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  relocation_taint_le next (tn with t_var := FEMPTY) (un with t_var := FEMPTY)
Proof
  simp[relocation_taint_le_def, demand_taint_def, op_taint_def] >>
  metis_tac[]
QED

(* Empty setup variable maps make this boundary independent of the new
   lookup, variable provenance and guarded-byte parameters. *)
Theorem layout_setup_local_rel:
  local_rel P ptr B R Obs s t /\ (!a b. next a b ==> R a b) /\
  setup_callee fn args s = SOME cs /\ setup_callee gn args' t = SOME ct /\
  Obs' cs ct ==>
  local_rel P' ptr' B' next Obs' cs ct
Proof
  strip_tac >> drule local_rel_demand >> strip_tac >>
  `demand_agree next (\a. read_byte a cs.vs_memory) (\b. read_byte b ct.vs_memory)` by
    (irule layout_setup_demand_agree >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  dxrule setup_callee_props >> strip_tac >>
  drule setup_callee_props >> strip_tac >>
  gvs[local_rel_def, variable_domains_def, variables_agree_on_def,
      local_values_def, lookup_var_def, FDOM_EQ_EMPTY]
QED

val _ = export_theory();
