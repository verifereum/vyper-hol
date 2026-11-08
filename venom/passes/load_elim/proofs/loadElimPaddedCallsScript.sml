Theory loadElimPaddedCalls
Ancestors
  loadElimPaddedNoncall loadElimPaddedSimHelpers loadElimMemoryRel
  loadElimPhiTransport venomExecSemantics venomState stateFrame stateEquiv
  list finite_map

Theorem le_padded_setup_total:
  padded_exec_equiv V s t /\ setup_callee fn args s = SOME c ==>
  ?d. setup_callee fn args t = SOME d /\ le_padded_control {} c d
Proof
  strip_tac >>
  `~NULL fn.fn_blocks` by gvs[setup_callee_def] >>
  simp[setup_callee_def, le_padded_control_def] >>
  conj_tac
  >- (irule padded_exec_equiv_setup_callee >>
      goal_assum (drule_at Any) >>
      qexistsl [`t`, `V`] >> simp[setup_callee_def]) >>
  gvs[setup_callee_def, le_padded_control_def]
QED

Theorem le_padded_bind_total:
  le_padded_control V s t /\ bind_outputs outs vals s = SOME u ==>
  ?v. bind_outputs outs vals t = SOME v /\ le_padded_control V u v
Proof
  strip_tac >>
  `LENGTH outs = LENGTH vals` by gvs[bind_outputs_def] >>
  gvs[bind_outputs_def] >>
  pop_assum kall_tac >>
  qpat_x_assum `le_padded_control V s t` mp_tac >>
  qid_spec_tac `t` >> qid_spec_tac `s` >>
  qspec_tac (`ZIP (outs,vals)`, `pairs`) >>
  Induct >- simp[] >>
  Cases_on `h` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  irule le_padded_control_update_var >> simp[]
QED

Theorem le_padded_control_idx:
  le_padded_control V s t ==>
  le_padded_control V (s with vs_inst_idx := n) (t with vs_inst_idx := n)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
       read_memory_def, execution_frame_def]
QED

Theorem le_padded_phis_total:
  le_padded_control {} s t /\ eval_phis s js = OK u ==>
  ?v. eval_phis t js = OK v /\ le_padded_control {} u v
Proof
  strip_tac >> irule le_eval_phis_transport >>
  conj_tac >- simp[le_padded_control_update_var] >>
  qexists_tac `s` >> simp[] >> rpt strip_tac >>
  irule le_eval_one_phi_agreement >>
  gvs[le_padded_control_def, padded_exec_equiv_def,
      execution_frame_def, venom_state_component_equality]
QED


Theorem le_padded_return_control:
  le_padded_control V s t /\ padded_exec_equiv callee_vars c d ==>
  le_padded_control V
    (adopt_return_fmp ir (merge_callee_state s c))
    (adopt_return_fmp ir (merge_callee_state t d))
Proof
  strip_tac >> rewrite_tac[le_padded_control_def] >> conj_tac
  >- (irule padded_exec_equiv_adopt_return >>
      irule padded_exec_equiv_merge_callee >>
      gvs[le_padded_control_def] >> metis_tac[]) >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def, le_padded_control_def]
QED

Theorem le_padded_full_weaken:
  padded_exec_equiv {} s t ==> padded_exec_equiv V s t
Proof
  simp[padded_exec_equiv_def]
QED

Theorem le_padded_invoke_return:
  le_padded_control V s t /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ eval_operands ops t = SOME args /\
  setup_callee fn args s = SOME c /\ setup_callee fn args t = SOME d /\
  ((?e. run_blocks fuel C fn c = Error e) \/
   lift_result (le_padded_control {}) (padded_exec_equiv {}) (padded_exec_equiv {})
     (run_blocks fuel C fn c) (run_blocks fuel C fn d)) ==>
  (?e. step_inst fuel C i s = Error e) \/
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst fuel C i s) (step_inst fuel C i t)
Proof
  strip_tac >> simp[step_inst_def] >>
  Cases_on `run_blocks fuel C fn c` >>
  Cases_on `run_blocks fuel C fn d` >>
  gvs[lift_result_def] >>
  simp[le_padded_full_weaken] >>
  qmatch_goalsub_rename_tac `bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cs))` >>
  rename1 `padded_exec_equiv {} cs ct` >>
  Cases_on `bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cs))` >>
  simp[lift_result_def] >>
  `le_padded_control V (adopt_return_fmp ret (merge_callee_state s cs))
    (adopt_return_fmp ret (merge_callee_state t ct))` by
      (irule le_padded_return_control >> metis_tac[]) >>
  drule_all le_padded_bind_total >> strip_tac >> simp[lift_result_def]
QED
