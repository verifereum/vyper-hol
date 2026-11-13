Theory concretizeLayoutLocalAssign
Ancestors frameRelocationCleanValueSteps
  concretizeLayoutLocalShifts frameRelocationGuardedSteps
  frameRelocationLocal frameRelocationGuardedValues frameRelocationTaintOrder
  frameRelocationGhostCopy frameOriginUpdates frameRelocationEnvironment
  concretizeLayoutReaderContext frameRelocationBinding frameJointDemand frameJointTrace
  ptrDiscipline venomExecSemantics venomState finite_map pred_set list

Theorem assign_execution_shape[local]:
  inst.inst_opcode = ASSIGN /\ inst.inst_outputs = [v] /\
  step_inst_base inst s = OK post ==>
  ?op x. inst.inst_operands = [op] /\ eval_operand op s = SOME x /\
    post = update_var v x s
Proof
  strip_tac >> qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem assign_literal_ghosts[local]:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [v] /\ (!w. op <> Var w) ==>
  step_prov PG (SND o_f rv) inst (update_var v x s) =
    SND o_f (origin_set rv [v] NONE) /\
  step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >>
  `new_site_bytes s (update_var v x s) = {}` by
    (irule frameRelocationMemoryTheory.new_site_bytes_unchanged >> simp[update_var_def]) >>
  Cases_on `op` >> gvs[] >> (conj_tac
  >- (simp[step_prov_def, out_prov_def, first_prov_def, op_prov_def,
           origin_set_def, set_prov_def, fmap_eq_flookup, FLOOKUP_o_f,
           FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> gen_tac >> IF_CASES_TAC >> simp[])) >>
  simp[step_taint_def, mem_taint_def,
       step_writes_def, codegenRelTheory.source_memory_write_ranges_def,
       written_taint_def, range_bytes_def, out_taint_def, op_taint_def,
       set_var_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
       eval_operand_def, AllCaseEqs(), taint_component_equality] >>
  Cases_on `FLOOKUP s.vs_labels s'` >> simp[]
QED

Theorem guarded_assign_variable[local]:
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  MEM inst (fn_insts fn) /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var w] /\
  inst.inst_outputs = [v] /\ lookup_var w s = SOME x /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  ?y. step_inst_base inst t = OK (update_var v y t) /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn) L (origin_set rv [v] (FLOOKUP rv w)))
      (guarded_bytes (retpc_var fn) (origin_set rv [v] (FLOOKUP rv w))
        (step_taint inst s (update_var v x s) tn)) next
      (\s t. dead_result_rel D (Halt s) (Halt t))
      (update_var v x s) (update_var v y t) /\
    step_prov PG (SND o_f rv) inst (update_var v x s) =
      SND o_f (origin_set rv [v] (FLOOKUP rv w)) /\
    relocation_taint_le next (step_taint inst s (update_var v x s) tn)
      (step_taint inst t (update_var v y t) un)
Proof
  strip_tac >>
  `!a b x y. dead_result_rel D (Halt a) (Halt b) ==>
    dead_result_rel D (Halt (update_var v x a)) (Halt (update_var v y b))` by
    simp[dead_result_rel_def, update_var_def] >>
  drule retpc_guarded_assign_step >> disch_then drule >> simp[] >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexists_tac `y` >> simp[] >> conj_tac
  >- (fs[local_rel_def, frameRelocationDemandTheory.demand_agree_def] >> metis_tac[]) >>
  `step_taint inst s (update_var v x s) tn =
    tn with t_var := tn.t_var |+ (v,op_taint tn (Var w))` by
    (irule assign_taint_copy >> simp[]) >>
  `step_taint inst t (update_var v y t) un =
    un with t_var := un.t_var |+ (v,op_taint un (Var w))` by
    (irule assign_taint_copy >> fs[eval_operand_def]) >>
  simp[] >> irule relocation_masked_write_taint >>
  conj_tac >- fs[relocation_taint_le_def] >> qexists_tac `R` >> simp[]
QED

Theorem guarded_assign_literal[local]:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  s.vs_labels = t.vs_labels /\ inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [op] /\ inst.inst_outputs = [v] /\
  (!w. op <> Var w) /\ eval_operand op s = SOME x /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  step_inst_base inst t = OK (update_var v x t) /\
  local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (step_taint inst s (update_var v x s) tn)) next
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var v x s) (update_var v x t) /\
  step_prov PG (SND o_f rv) inst (update_var v x s) =
    SND o_f (origin_set rv [v] NONE) /\
  relocation_taint_le next (step_taint inst s (update_var v x s) tn)
    (step_taint inst t (update_var v x t) un)
Proof
  strip_tac >>
  `eval_operand op t = SOME x` by
    (Cases_on `op` >> gvs[eval_operand_def]) >>
  `step_taint inst s (update_var v x s) tn = tn with t_var := tn.t_var |+ (v,{})` by
    metis_tac[assign_literal_ghosts] >>
  `step_taint inst t (update_var v x t) un = un with t_var := un.t_var |+ (v,{})` by
    metis_tac[assign_literal_ghosts] >>
  simp[] >> conj_tac
  >- (pure_once_rewrite_tac[step_inst_base_def] >>
      asm_rewrite_tac[venomInstTheory.opcode_case_def] >> simp[]) >>
  conj_tac
  >- (irule guarded_masked_write_restrict >> simp[word_agree_except_def] >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[assign_literal_ghosts] >>
  irule relocation_masked_write_taint >> simp[] >> qexists_tac `R` >> simp[]
QED

Theorem guarded_assign_step[local]:
  local_rel (\u. F) (guarded_ptr (retpc_var fn) L rv)
    (guarded_bytes (retpc_var fn) rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  MEM inst (fn_insts fn) /\ s.vs_labels = t.vs_labels /\
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [v] /\ eval_operand op s = SOME x /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) ==>
  ?y. step_inst_base inst t = OK (update_var v y t) /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn) L
        (origin_set rv [v] (case op of Var w => FLOOKUP rv w | _ => NONE)))
      (guarded_bytes (retpc_var fn)
        (origin_set rv [v] (case op of Var w => FLOOKUP rv w | _ => NONE))
        (step_taint inst s (update_var v x s) tn)) next
      (\s t. dead_result_rel D (Halt s) (Halt t))
      (update_var v x s) (update_var v y t) /\
    step_prov PG (SND o_f rv) inst (update_var v x s) =
      SND o_f (origin_set rv [v] (case op of Var w => FLOOKUP rv w | _ => NONE)) /\
    relocation_taint_le next (step_taint inst s (update_var v x s) tn)
      (step_taint inst t (update_var v y t) un)
Proof
  strip_tac >> Cases_on `op` >> fs[]
  >- (qexists_tac `x` >> irule guarded_assign_literal >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- (irule guarded_assign_variable >> fs[eval_operand_def] >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists_tac `x` >> irule guarded_assign_literal >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem concretize_assign_local_complete:
  vs0.vs_allocas = FEMPTY /\ ptr_discipline lo C vs0 /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  resolved_config_ok (JointConfig stk PG G tn fn inst s oms om hs h)
    (birth::ids) ((rp,rv)::anns) /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\
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
  ?op rv' tpost. inst.inst_operands = [op] /\
    rv' = origin_set rv [v] (case op of Var w => FLOOKUP rv w | _ => NONE) /\
    step_inst_base inst t = OK tpost /\
    local_rel (\u. F)
      (guarded_ptr (retpc_var fn)
        (activation_lookup (0:num) (concretize_positions C')
          (birth::ids) (fn::MAP (\f. f.cf_fn) stk)) rv')
      (guarded_bytes (retpc_var fn) rv' (step_taint inst s post tn))
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (\s t. dead_result_rel D (Halt s) (Halt t)) post tpost /\
    step_prov PG (SND o_f rv) inst post = SND o_f rv' /\
    relocation_taint_le
      (joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c))
      (step_taint inst s post tn) (step_taint inst t tpost un) /\
    relocation_env post tpost /\ relocation_reader_context post tpost
Proof
  strip_tac >>
  `?op x. inst.inst_operands = [op] /\ eval_operand op s = SOME x /\
    post = update_var v x s` by metis_tac[assign_execution_shape] >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def,
          codegenRelTheory.source_memory_write_ranges_def, range_bytes_def] >> metis_tac[]) >>
  `s.vs_labels = t.vs_labels` by fs[relocation_env_def] >>
  drule_all guarded_assign_step >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl_tac [`op`, `origin_set rv [v] (case op of Var w => FLOOKUP rv w | _ => NONE)`,
               `update_var v y t`] >> simp[] >>
  qpat_x_assum `post = _` SUBST_ALL_TAC >>
  simp[relocation_env_update_var, relocation_reader_context_update_var]
QED
