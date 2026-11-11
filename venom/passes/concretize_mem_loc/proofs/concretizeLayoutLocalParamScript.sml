Theory concretizeLayoutLocalParam
Ancestors concretizeLayoutParameterSteps concretizeLayoutParameterRoots
  concretizeLayoutCalleeRoots concretizeLayoutLocalRetpc concretizeLayoutReaderContext
  frameResolvedOrigins frameOriginUpdates frameRelocationLocal
  frameRelocationGuardedValues frameRelocationTaintOrder frameRelocationEnvironment
  frameRelocationDemand frameRelocationBinding frameJointDemand frameJointTrace
  ptrDiscipline venomExecSemantics venomState finite_map pred_set list words

Theorem parameter_execution_shape[local]:
  inst.inst_opcode = PARAM /\ inst.inst_outputs = [out] /\
  step_inst_base inst s = OK post ==>
  ?idx. inst.inst_operands = [Lit idx] /\ w2n idx < LENGTH s.vs_params /\
    post = update_var out (EL (w2n idx) s.vs_params) s
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[] >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem concretize_param_local_complete:
  vs0.vs_allocas = FEMPTY /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = PARAM /\ inst.inst_outputs = [out] /\
  MEM inst (fn_insts fn) /\ step_inst_base inst s = OK post /\
  parameter_roots (\i x y. clean_resolved_root
    (activation_lookup (0:num) (concretize_positions C')
      (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (resolved_parameter_entry rp i) x y)
    s.vs_params t.vs_params /\
  PG = MAP (OPTION_MAP SND) rp /\
  resolution ct rp om rv /\
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
  ?idx rv' tpost. inst.inst_operands = [Lit idx] /\
    w2n idx < LENGTH s.vs_params /\
    rv' = origin_set rv [out] (resolved_parameter_entry rp (w2n idx)) /\
    step_inst_base inst t = OK tpost /\
    resolution ct rp (origin_step PG om inst post) rv' /\
    step_prov PG (SND o_f rv) inst post = SND o_f rv' /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv')
      (guarded_bytes (retpc_var fn) rv' (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    parameter_roots (\i x y. clean_resolved_root
      (activation_lookup (0:num) (concretize_positions C')
        (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) (resolved_parameter_entry rp i) x y)
      post.vs_params tpost.vs_params /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >> drule_all parameter_execution_shape >> strip_tac >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def,
          codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >> metis_tac[]) >>
  `!a b x y. dead_result_rel D (Halt a) (Halt b) ==>
    dead_result_rel D (Halt (update_var out x a)) (Halt (update_var out y b))` by
    simp[dead_result_rel_def, update_var_def] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) resolved_parameter_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  disch_then (drule_at (Pat `resolution _ _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[] >> strip_tac >>
  `step_prov PG (SND o_f rv) inst post =
    SND o_f (origin_set rv [out] (resolved_parameter_entry rp (w2n idx)))` by
    (imp_res_tac resolution_erasure >> gvs[origin_step_erase]) >>
  `relocation_env post post' /\ relocation_reader_context post post'` by
    (drule_all parameter_execution_shape >> strip_tac >>
     gvs[] >> simp[relocation_env_update_var, relocation_reader_context_update_var]) >>
  qpat_x_assum `post = _` SUBST_ALL_TAC >>
  qpat_x_assum `PG = _` SUBST_ALL_TAC >>
  qexists_tac `post'` >> simp[] >> conj_tac
  >- (fs[local_rel_def, demand_agree_def] >> metis_tac[]) >>
  fs[relocation_taint_le_def, frameRelocationCopyTaintTheory.demand_taint_def] >> metis_tac[]
QED
