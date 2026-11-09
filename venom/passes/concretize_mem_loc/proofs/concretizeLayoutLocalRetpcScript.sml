Theory concretizeLayoutLocalRetpc
Ancestors concretizeLayoutLocalInitialFmp concretizeLayoutParameterRoots
  frameRelocationGuardedValues frameRelocationGhostCopy frameRelocationLocal unitShapeDefs
  concretizeLayoutReaderContext frameRelocationEnvironment frameRelocationBinding
  frameJointDemand frameRelocationCleanValueSteps frameRelocationMemory frameRelocationDemand
  frameOriginUpdates frameJointTrace frameJointTransition frameJointTaint
  ptrDiscipline venomExecSemantics venomState codegenRel finite_map pred_set list

Theorem guarded_opaque_write_restrict:
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  Opaque v /\ (!a b. next a b ==> R a b) ==>
  local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,{}))) next
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var v x s) (update_var v y t)
Proof
  strip_tac >>
  `local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
    (guarded_bytes Opaque (origin_set rv [v] NONE)
      (tn with t_var := tn.t_var |+ (v,{}))) R
    (\s t. dead_result_rel D (Halt s) (Halt t))
    (update_var v x s) (update_var v y t)` by
    (irule local_rel_update_observation_invariant >>
     simp[guarded_ptr_def, guarded_bytes_def] >>
     conj_tac
     >- simp[update_var_def, dead_result_rel_def] >>
     goal_assum (drule_at Any) >>
     simp[guarded_ptr_def, guarded_bytes_def, copy_ptr_other, copy_bytes_other]) >>
  fs[local_rel_def, demand_agree_def] >> metis_tac[]
QED

Theorem retpc_execution[local]:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [v] /\
  step_inst_base inst s = OK post ==>
  (?idx. inst.inst_operands = [Lit idx]) /\
  post = update_var v s.vs_return_pc_token s
Proof
  strip_tac >> qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[] >> Cases_on `t` >> simp[]
QED

Theorem retpc_ghosts[local]:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [v] /\
  inst.inst_operands = [Lit idx] ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
  step_taint inst s (update_var v z s) tn = tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >> (conj_tac
  >- (simp[step_prov_def, out_prov_def, set_prov_def,
           origin_set_def, fmap_eq_flookup, FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
      gen_tac >> IF_CASES_TAC >> simp[])) >>
  `new_site_bytes s (update_var v z s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality, eval_operand_def]
QED

Theorem concretize_retpc_param_local_complete:
  vs0.vs_allocas = FEMPTY /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [v] /\
  MEM inst (fn_insts fn) /\ step_inst_base inst s = OK post /\
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
  `retpc_var fn v` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!a b. joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c) a b ==>
         joint_relocation_demand lo (concretize_positions C') q0 es qs c a b` by
    (rpt strip_tac >> irule joint_relocation_demand_retained >>
     goal_assum (drule_at Any) >>
     simp[joint_writes_def, step_writes_def, source_memory_write_ranges_def,
          range_bytes_def] >> metis_tac[]) >>
  drule_all retpc_execution >> strip_tac >>
  drule_all parameter_roots_retpc_read >> strip_tac >>
  qexists_tac `update_var v t.vs_return_pc_token t` >> simp[] >>
  `step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})` by
    (gvs[] >> metis_tac[retpc_ghosts]) >>
  `step_taint inst t (update_var v t.vs_return_pc_token t) un = un with t_var := un.t_var |+ (v,{})` by
    metis_tac[retpc_ghosts] >>
  simp[retpc_ghosts] >> conj_tac
  >- (gvs[] >> irule guarded_opaque_write_restrict >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (irule relocation_clean_write_taint >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> conj_tac
  >- (irule relocation_env_update_var >> simp[]) >>
  irule relocation_reader_context_update_var >> simp[]
QED

val _ = if null (hyp concretize_retpc_param_local_complete) then ()
        else raise Fail "RETPC_PARAM export has hypotheses";
val _ = export_theory();
