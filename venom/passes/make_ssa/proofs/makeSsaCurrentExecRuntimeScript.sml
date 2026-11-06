Theory makeSsaCurrentExecRuntime
Ancestors
  makeSsaCurrentRuntime o1FrameLockstep venomExecProps venomExecProofs
  venomInstProps venomWf venomState venomExecSemantics stateFrame finite_map list pred_set

Theorem current_exec_lookup_unwritten:
  step_inst fuel C inst st = OK t /\ ~MEM v inst.inst_outputs ==>
  lookup_var v t = lookup_var v st
Proof
  strip_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_terminator_preserves_vars] >>
  metis_tac[step_preserves_non_output_vars]
QED

Theorem current_exec_lookup_written:
  step_inst fuel C inst st = OK t /\ inst_wf inst /\
  inst.inst_opcode <> PHI /\ MEM v inst.inst_outputs ==>
  IS_SOME (lookup_var v t)
Proof
  strip_tac >>
  `~is_terminator inst.inst_opcode` by metis_tac[terminator_no_outputs, MEM] >>
  drule_all step_inst_fdom >> strip_tac >>
  fs[lookup_var_def, FLOOKUP_DEF]
QED

Theorem current_exec_update_last_slots:
  state_rel sg st st' /\ current_last_output_slots sg [out] [out'] sg1 ==>
  state_rel sg1 (update_var out value st) (update_var out' value st')
Proof
  strip_tac >>
  `bind_outputs [out'] [value] st' = SOME (update_var out' value st')` by
    simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >> simp[bind_outputs_def]
QED

Theorem current_exec_pure1_pair:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure1 f inst' st' = OK t' ==>
  ?t. exec_pure1 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure1_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_pure2_pair:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure2 f inst' st' = OK t' ==>
  ?t. exec_pure2 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure2_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_pure3_pair:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure3 f inst' st' = OK t' ==>
  ?t. exec_pure3 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure3_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_read0_pair:
  (!a b. execution_frame a = execution_frame b ==> f a = f b) /\
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_read0 f inst' st' = OK t' ==>
  ?t. exec_read0 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> fs[exec_read0_def, AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  `f st = f st'` by (first_x_assum irule >> fs[state_rel_def]) >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_read1_pair:
  (!v a b. execution_frame a = execution_frame b ==> f v a = f v b) /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_read1 f inst' st' = OK t' ==>
  ?t. exec_read1 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_read1_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  `!v. f v st = f v st'` by
    (gen_tac >> first_x_assum irule >> fs[state_rel_def]) >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_empty_last_slots:
  state_rel sg st st' /\ current_last_output_slots sg [] [] sg1 ==>
  state_rel sg1 st st'
Proof
  strip_tac >>
  `bind_outputs [] [] st' = SOME st'` by simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >> simp[bind_outputs_def]
QED

Theorem current_exec_write2_pair:
  (!x y a b. state_rel sg a b ==> state_rel sg (f x y a) (f x y b)) /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  inst.inst_outputs = [] /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_write2 f inst' st' = OK t' ==>
  ?t. exec_write2 f inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_write2_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `inst'.inst_outputs = []` by fs[current_last_output_slots_def] >>
  gvs[] >>
  metis_tac[current_exec_empty_last_slots]
QED

Theorem current_exec_gas_pair:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_gas inst' st' = OK t' ==>
  ?t. exec_gas inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `st'.vs_gas_readings = st.vs_gas_readings` by
    fs[state_rel_def, execution_frame_def] >>
  fs[exec_gas_def, AllCaseEqs()] >>
  `LENGTH inst.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[]
  >- metis_tac[current_exec_update_last_slots] >>
  irule current_exec_update_last_slots >>
  qexists_tac `sg` >> simp[] >>
  fs[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED

Theorem current_exec_bump_pair:
  inst.inst_opcode = BUMP /\ inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  step_inst_base inst' st' = OK t' ==>
  ?t. step_inst_base inst st = OK t /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  `inst'.inst_opcode = BUMP` by fs[inst_pair_def] >>
  fs[Once step_inst_base_def, AllCaseEqs()] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  `LENGTH inst.inst_outputs = 2` by fs[current_last_output_slots_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  rename1 `inst.inst_outputs = out1::rest` >> Cases_on `rest` >> gvs[] >>
  rename1 `inst.inst_outputs = [out1;out2]` >>
  rename1 `inst'.inst_outputs = [out1';out2']` >>
  rename1 `update_var out2' (bv + szv) (update_var out1' bv st')` >>
  `bind_outputs [out1';out2'] [bv;word_add bv szv] st' =
    SOME (update_var out2' (word_add bv szv) (update_var out1' bv st'))` by
    simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >>
  simp[bind_outputs_def, Once step_inst_base_def] >> metis_tac[]
QED

