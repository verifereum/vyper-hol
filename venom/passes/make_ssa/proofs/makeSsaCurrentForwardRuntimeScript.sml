Theory makeSsaCurrentForwardRuntime
Ancestors
  makeSsaCurrentRuntime makeSsaCurrentExecRuntime o1FrameLockstep venomExecSemantics
  stateFrame venomState

Theorem current_runtime_bind_last_slots_forward:
  state_rel sg st st' /\ current_last_output_slots sg outs outs' sg1 /\
  bind_outputs outs vals st = SOME t ==>
  ?t'. bind_outputs outs' vals st' = SOME t' /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `LENGTH outs = LENGTH outs'` by fs[current_last_output_slots_def] >>
  `LENGTH outs = LENGTH vals` by fs[bind_outputs_def] >>
  `?t'. bind_outputs outs' vals st' = SOME t'` by simp[bind_outputs_def] >>
  drule_all current_runtime_bind_last_slots >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem current_exec_pure1_pair_forward:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure1 f inst st = OK t ==>
  ?t'. exec_pure1 f inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure1_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[] >>
  `LENGTH inst'.inst_outputs = 1` by
    fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_pure1_undefined_forward:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  exec_pure1 f inst st = Error "undefined operand" ==>
  exec_pure1 f inst' st' = Error "undefined operand"
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure1_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[]
QED

Theorem current_invoke_decode_args_pair:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  decode_invoke inst = SOME (nm, ops) ==>
  ?ops'. decode_invoke inst' = SOME (nm, ops') /\
    eval_operands ops' st' = eval_operands ops st
Proof
  strip_tac >> drule_all inst_pair_ops >>
  gvs[decode_invoke_def, AllCaseEqs(), ops_pair_def] >>
  strip_tac >>
  `op' = Label nm` by (Cases_on `op'` >> fs[op_rename_def]) >>
  gvs[] >> metis_tac[eval_operands_rel]
QED

Theorem current_exec_pure2_pair_forward:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure2 f inst st = OK t ==>
  ?t'. exec_pure2 f inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure2_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_pure3_pair_forward:
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_pure3 f inst st = OK t ==>
  ?t'. exec_pure3 f inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_pure3_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_read0_pair_forward:
  (!a b. execution_frame a = execution_frame b ==> f a = f b) /\
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_read0 f inst st = OK t ==>
  ?t'. exec_read0 f inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> fs[exec_read0_def, AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  `f st = f st'` by (first_x_assum irule >> fs[state_rel_def]) >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_read1_pair_forward:
  (!v a b. execution_frame a = execution_frame b ==> f v a = f v b) /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_read1 f inst st = OK t ==>
  ?t'. exec_read1 f inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_read1_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[] >>
  `!v. f v st = f v st'` by
    (gen_tac >> first_x_assum irule >> fs[state_rel_def]) >>
  metis_tac[current_exec_update_last_slots]
QED

Theorem current_exec_write2_pair_forward:
  (!x y a b. state_rel sg a b ==> state_rel sg (f x y a) (f x y b)) /\
  inst_pair sg inst inst' /\ state_rel sg st st' /\
  inst.inst_outputs = [] /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_write2 f inst st = OK t ==>
  ?t'. exec_write2 f inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >> drule_all inst_pair_ops >>
  simp[ops_pair_def] >> strip_tac >>
  fs[exec_write2_def, AllCaseEqs()] >>
  Cases_on `inst'.inst_operands` >> gvs[] >>
  `inst'.inst_outputs = []` by fs[current_last_output_slots_def] >>
  gvs[] >> metis_tac[current_exec_empty_last_slots]
QED

Theorem current_exec_gas_pair_forward:
  state_rel sg st st' /\
  current_last_output_slots sg inst.inst_outputs inst'.inst_outputs sg1 /\
  exec_gas inst st = OK t ==>
  ?t'. exec_gas inst' st' = OK t' /\ state_rel sg1 t t'
Proof
  strip_tac >>
  `st'.vs_gas_readings = st.vs_gas_readings` by
    fs[state_rel_def, execution_frame_def] >>
  fs[exec_gas_def, AllCaseEqs()] >>
  `LENGTH inst'.inst_outputs = 1` by fs[current_last_output_slots_def] >>
  Cases_on `inst'.inst_outputs` >> gvs[]
  >- metis_tac[current_exec_update_last_slots] >>
  irule current_exec_update_last_slots >>
  qexists_tac `sg` >> simp[] >>
  fs[state_rel_def, execution_frame_def, vars_rel_def, lookup_var_def]
QED
