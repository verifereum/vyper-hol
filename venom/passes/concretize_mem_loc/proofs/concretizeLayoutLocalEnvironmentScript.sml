Theory concretizeLayoutLocalEnvironment
Ancestors frameRelocationEnvironment frameRelocationBinding frameJointDemand
  concretizeLayoutLocalValues ptrDiscipline codegenRel finite_map
  venomExecSemantics venomState frameRelocationCleanValueSteps
  frameRelocationGuardedValues frameRelocationLocal frameRelocationTaintOrder
  frameRelocationMemory

Theorem callcontext_reader_execution[local]:
  (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS) /\
  inst.inst_outputs = [v] /\ relocation_env s t /\
  step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t) /\
    relocation_env post (update_var v z t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_read0_def] >> strip_tac >> gvs[relocation_env_def] >>
  simp[relocation_env_def, update_var_def] >> metis_tac[]
QED

Theorem callcontext_reader_ghosts[local]:
  (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS) /\
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
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  namedCases_on `t` ["", "b args2"] >> simp[] >>
  namedCases_on `args2` ["", "c args3"] >> simp[] >>
  Cases_on `args3` >> simp[]
QED

Theorem guarded_callcontext_reader_step:
  (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS) /\
  inst.inst_outputs = [v] /\ relocation_env s t /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) /\
  step_inst_base inst s = OK post ==>
  ?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t) /\
    relocation_env post (update_var v z t) /\
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
  `?z. post = update_var v z s /\
    step_inst_base inst t = OK (update_var v z t) /\
    relocation_env post (update_var v z t)` by
    (irule callcontext_reader_execution >> simp[]) >>
  qexists_tac `z` >> simp[] >>
  `step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
   step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})` by
    (gvs[] >> metis_tac[callcontext_reader_ghosts]) >>
  `step_taint inst t (update_var v z t) un = un with t_var := un.t_var |+ (v,{})` by
    metis_tac[callcontext_reader_ghosts] >>
  simp[] >> (conj_tac
  >- (gvs[] >> simp[callcontext_reader_ghosts] >>
      irule guarded_clean_write_restrict >> simp[] >>
      metis_tac[])) >>
  simp[callcontext_reader_ghosts] >>
  irule relocation_clean_write_taint >> goal_assum (drule_at Any) >> simp[]
QED

Theorem env_reader_no_writes[local]:
  (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS \/
   inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) ==>
  step_writes inst s post = []
Proof
  strip_tac >> simp[step_writes_def, source_memory_write_ranges_def]
QED

Theorem concretize_env_reader_local_complete:
  vs0.vs_allocas = FEMPTY /\
  joint_trace vs0 C q0 es qs q /\ c < LENGTH es /\
  EL c (q0::qs) = JointConfig stk PG G tn fn inst s oms om hs h /\
  EL c es = SOME (OriginOrdinary fuel post) /\
  (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS \/
   inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) /\
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
  all_tac
  >~ [`inst.inst_opcode = CALLER`] >- suspend "callcontext"
  >~ [`inst.inst_opcode = ADDRESS`] >- suspend "callcontext" >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_env_reader_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c)`, `PG`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `update_var v z (t with vs_gas_readings := rest)` >> simp[]
QED

Resume concretize_env_reader_local_complete[callcontext]:
  markerLib.RESUME_TAC >> (all_tac >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) guarded_callcontext_reader_step >>
  disch_then (drule_at (Pat `step_inst_base _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`joint_relocation_demand lo (concretize_positions C') q0 es qs (SUC c)`, `PG`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `update_var v z t` >> simp[])
QED
Finalise concretize_env_reader_local_complete

val _ = if null (hyp concretize_env_reader_local_complete) then ()
        else raise Fail "environment reader export has hypotheses";
