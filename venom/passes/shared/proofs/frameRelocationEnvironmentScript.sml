Theory frameRelocationEnvironment
Ancestors frameRelocationCleanValueSteps frameRelocationLocal
  frameRelocationGuardedValues frameRelocationDemand frameRelocationMemory
  ptrDiscipline venomExecSemantics venomState finite_map

(* Deliberately not a complete execution/frame invariant. *)
Definition relocation_env_def:
  relocation_env s t <=>
    s.vs_labels = t.vs_labels /\
    s.vs_call_ctx = t.vs_call_ctx /\
    s.vs_gas_readings = t.vs_gas_readings
End

Theorem relocation_env_refl[simp]:
  relocation_env s s
Proof
  simp[relocation_env_def]
QED

Theorem relocation_env_update_var:
  relocation_env s t ==>
  relocation_env (update_var v x s) (update_var w y t)
Proof
  simp[relocation_env_def, update_var_def]
QED

Theorem relocation_env_gas_tail:
  relocation_env s t ==>
  relocation_env (s with vs_gas_readings := rest)
    (t with vs_gas_readings := rest)
Proof
  simp[relocation_env_def]
QED

Theorem relocation_env_reader_execution:
  (inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) /\
  inst.inst_outputs = [v] /\ relocation_env s t /\
  step_inst_base inst s = OK post ==>
  ?z rest. post = update_var v z (s with vs_gas_readings := rest) /\
    step_inst_base inst t = OK (update_var v z (t with vs_gas_readings := rest)) /\
    relocation_env post (update_var v z (t with vs_gas_readings := rest))
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK post` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  fs[relocation_env_def]
  >- (asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
      simp[exec_read0_def] >> strip_tac >> gvs[] >>
      qexists_tac `t.vs_call_ctx.cc_callvalue` >>
      simp[relocation_env_def, update_var_def, venom_state_component_equality]) >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_gas_def] >>
  namedCases_on `s.vs_gas_readings` ["", "reading rest"] >> gvs[] >>
  strip_tac >> gvs[]
  >- (qexists_tac `0w` >>
      simp[relocation_env_def, update_var_def, venom_state_component_equality]) >>
  qpat_x_assum `reading::rest = t.vs_gas_readings` (assume_tac o SYM) >>
  gvs[] >> qexists_tac `reading` >>
  simp[relocation_env_def, update_var_def]
QED

Theorem local_rel_gas_readings:
  local_rel P ptr B R (\s t. dead_result_rel D (Halt s) (Halt t)) s t ==>
  local_rel P ptr B R (\s t. dead_result_rel D (Halt s) (Halt t))
    (s with vs_gas_readings := rs) (t with vs_gas_readings := rt)
Proof
  simp[local_rel_def, frameRelocationValuesTheory.variable_domains_def,
       frameRelocationValuesTheory.variables_agree_on_def, local_values_def,
       lookup_var_def, dead_result_rel_def]
QED

Theorem reader_clean_ghosts:
  (inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) /\
  inst.inst_outputs = [v] ==>
  step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
  step_taint inst s (update_var v z (s with vs_gas_readings := rest)) tn =
    tn with t_var := tn.t_var |+ (v,{})
Proof
  strip_tac >> (conj_tac
  >- (simp[step_prov_def, out_prov_def, set_prov_def,
           frameOriginUpdatesTheory.origin_set_def, fmap_eq_flookup,
           FLOOKUP_o_f, FLOOKUP_DRESTRICT] >>
      gen_tac >> IF_CASES_TAC >> simp[])) >>
  `new_site_bytes s (update_var v z (s with vs_gas_readings := rest)) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, store_taint_def, adopt_reset_def, imm_taint_def,
       out_taint_def, set_var_taint_def, taint_component_equality] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `eval_operand h s` >> simp[] >>
  namedCases_on `t` ["", "b args2"] >> simp[] >>
  namedCases_on `args2` ["", "c args3"] >> simp[] >>
  Cases_on `args3` >> simp[]
QED

Theorem guarded_env_reader_step:
  (inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS) /\
  inst.inst_outputs = [v] /\ relocation_env s t /\
  local_rel (\u. F) (guarded_ptr Opaque L rv)
    (guarded_bytes Opaque rv tn) R
    (\s t. dead_result_rel D (Halt s) (Halt t)) s t /\
  relocation_taint_le R tn un /\ (!a b. next a b ==> R a b) /\
  step_inst_base inst s = OK post ==>
  ?z rest. post = update_var v z (s with vs_gas_readings := rest) /\
    step_inst_base inst t = OK (update_var v z (t with vs_gas_readings := rest)) /\
    relocation_env post (update_var v z (t with vs_gas_readings := rest)) /\
    local_rel (\u. F) (guarded_ptr Opaque L (origin_set rv [v] NONE))
      (guarded_bytes Opaque (origin_set rv [v] NONE)
        (step_taint inst s post tn)) next
      (\s t. dead_result_rel D (Halt s) (Halt t))
      post (update_var v z (t with vs_gas_readings := rest)) /\
    step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
    relocation_taint_le next (step_taint inst s post tn)
      (step_taint inst t (update_var v z (t with vs_gas_readings := rest)) un)
Proof
  strip_tac >>
  `?z rest. post = update_var v z (s with vs_gas_readings := rest) /\
    step_inst_base inst t = OK (update_var v z (t with vs_gas_readings := rest)) /\
    relocation_env post (update_var v z (t with vs_gas_readings := rest))` by
    (irule relocation_env_reader_execution >> simp[]) >>
  qexistsl_tac [`z`, `rest`] >> simp[] >>
  `step_prov PG (SND o_f rv) inst post = SND o_f (origin_set rv [v] NONE) /\
   step_taint inst s post tn = tn with t_var := tn.t_var |+ (v,{})` by
    (gvs[] >> metis_tac[reader_clean_ghosts]) >>
  `step_taint inst t (update_var v z (t with vs_gas_readings := rest)) un =
    un with t_var := un.t_var |+ (v,{})` by metis_tac[reader_clean_ghosts] >>
  simp[] >> (conj_tac
  >- (gvs[] >> simp[reader_clean_ghosts] >>
      irule guarded_clean_write_restrict >> simp[] >>
      goal_assum (drule_at Any) >>
      irule local_rel_gas_readings >> goal_assum (drule_at Any))) >>
  simp[reader_clean_ghosts] >>
  irule relocation_clean_write_taint >> goal_assum (drule_at Any) >> simp[]
QED
