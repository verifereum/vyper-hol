Theory readonlyInvokeCopyFwdStepsEffects
Ancestors
  readonlyInvokeCopyFwdStepsCore readonlyInvokeCopyFwdEffects readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdRel taintAgree venomState venomExecSemantics
  internalReturnCopyFwdSim ptrDiscipline finite_map words list pred_set

(* Shared effects do not change the provenance-bearing locals or memory.
   The effect premise owns precisely the changed shared fields. *)
Theorem ricf_frame_shared_effect:
  ricf_frame_agree D X sites PG H tn s t /\
  ricf_effect_agree D X un u v /\
  u.vs_vars = s.vs_vars /\ v.vs_vars = t.vs_vars /\
  u.vs_params = s.vs_params /\ v.vs_params = t.vs_params /\
  u.vs_memory = s.vs_memory /\ v.vs_memory = t.vs_memory /\
  un.t_var = tn.t_var /\ un.t_mem = tn.t_mem ==>
  ricf_frame_agree D X sites PG H un u v
Proof
  simp[ricf_frame_agree_def, ricf_effect_agree_def, op_taint_def,
       ircf_cross_def] >> metis_tac[]
QED

Theorem ricf_frame_sstore:
  ricf_frame_agree D X sites PG H tn s t /\ word_agree_except m x y ==>
  ricf_frame_agree D X sites PG H
    (tn with t_stor := key_update tn.t_stor key m)
    (sstore key x s) (sstore key y t)
Proof
  strip_tac >> irule ricf_frame_shared_effect >>
  conj_tac >- metis_tac[ricf_frame_effect, ricf_effect_sstore] >>
  qexistsl [`s`, `t`, `tn`] >> simp[sstore_def]
QED

Theorem ricf_frame_tstore:
  ricf_frame_agree D X sites PG H tn s t /\ word_agree_except m x y ==>
  ricf_frame_agree D X sites PG H
    (tn with t_trans := key_update tn.t_trans key m)
    (tstore key x s) (tstore key y t)
Proof
  strip_tac >> irule ricf_frame_shared_effect >>
  conj_tac >- metis_tac[ricf_frame_effect, ricf_effect_tstore] >>
  qexistsl [`s`, `t`, `tn`] >> simp[tstore_def]
QED

Theorem ricf_cert_sstore:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  word_agree_except m x y /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL j targets).vs_call_ctx.cc_address = t.vs_call_ctx.cc_address) ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (sstore key x s) H)
    (ricf_effective_taint fn (sstore key x s)
      (un with t_stor := key_update un.t_stor key m)) fn
    sites maps targets H (un with t_stor := key_update un.t_stor key m)
    cur curs (sstore key x s) (sstore key y t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (gvs[ircf_cross_def, sstore_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def, sstore_def] >> metis_tac[])
  >- (drule_all ricf_frame_sstore >>
      disch_then (qspec_then `key` mp_tac) >>
      simp[sstore_def, ircf_dead_def])
  >> fs[ricf_live_stack_agree_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  drule_all ricf_frame_sstore >>
  disch_then (qspec_then `key` mp_tac) >>
  simp[merge_callee_state_def, sstore_def]
QED

Theorem ricf_cert_tstore:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  word_agree_except m x y /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL j targets).vs_call_ctx.cc_address = t.vs_call_ctx.cc_address) ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (tstore key x s) H)
    (ricf_effective_taint fn (tstore key x s)
      (un with t_trans := key_update un.t_trans key m)) fn
    sites maps targets H (un with t_trans := key_update un.t_trans key m)
    cur curs (tstore key x s) (tstore key y t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (gvs[ircf_cross_def, tstore_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def, tstore_def] >> metis_tac[])
  >- (drule_all ricf_frame_tstore >>
      disch_then (qspec_then `key` mp_tac) >>
      simp[tstore_def, ircf_dead_def])
  >> fs[ricf_live_stack_agree_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  drule_all ricf_frame_tstore >>
  disch_then (qspec_then `key` mp_tac) >>
  simp[merge_callee_state_def, tstore_def]
QED

Theorem ricf_frame_returndata:
  ricf_frame_agree D X sites PG H tn s t ==>
  ricf_frame_agree D X sites PG H tn (set_returndata rd s) (set_returndata rd t)
Proof
  strip_tac >> irule ricf_frame_shared_effect >>
  conj_tac >- metis_tac[ricf_frame_effect, ricf_effect_returndata] >>
  qexistsl [`s`, `t`, `tn`] >> simp[set_returndata_def]
QED

Theorem ricf_cert_returndata:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (set_returndata rd s) H)
    (ricf_effective_taint fn (set_returndata rd s) un) fn
    sites maps targets H un cur curs (set_returndata rd s) (set_returndata rd t)
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (gvs[ircf_cross_def, set_returndata_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def, set_returndata_def] >> metis_tac[])
  >- (drule ricf_frame_returndata >> disch_then (qspec_then `rd` mp_tac) >>
      simp[set_returndata_def, ircf_dead_def])
  >> fs[ricf_live_stack_agree_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ricf_frame_returndata >> disch_then (qspec_then `rd` mp_tac) >>
  simp[merge_callee_state_def, set_returndata_def]
QED

Theorem ricf_frame_gas_tail:
  ricf_frame_agree D X sites PG H tn s t ==>
  ricf_frame_agree D X sites PG H tn
    (s with vs_gas_readings := rest) (t with vs_gas_readings := rest)
Proof
  strip_tac >> irule ricf_frame_shared_effect >>
  conj_tac >- metis_tac[ricf_frame_effect, ricf_effect_gas_tail] >>
  qexistsl [`s`, `t`, `tn`] >> simp[]
QED

Theorem ricf_cert_gas_tail:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t ==>
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (s with vs_gas_readings := rest) H)
    (ricf_effective_taint fn (s with vs_gas_readings := rest) un) fn
    sites maps targets H un cur curs
    (s with vs_gas_readings := rest) (t with vs_gas_readings := rest)
Proof
  strip_tac >>
  qpat_x_assum `ricf_cert_core _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ricf_cert_core_def, ricf_live_boundary_core_def]) >>
  irule ricf_cert_reconstruct >> rpt conj_tac
  >- (gvs[ircf_cross_def] >> metis_tac[])
  >- (gvs[ricf_cert_crosses_def, EVERY_MEM, ircf_cross_def] >> metis_tac[])
  >- (drule ricf_frame_gas_tail >> disch_then (qspec_then `rest` mp_tac) >>
      simp[ircf_dead_def])
  >> fs[ricf_live_stack_agree_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule ricf_frame_gas_tail >> disch_then (qspec_then `rest` mp_tac) >>
  simp[merge_callee_state_def]
QED

Theorem ricf_cert_step_sstore:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  inst.inst_opcode = SSTORE /\ inst.inst_operands = [a;b] /\
  eval_operand a s = SOME key /\ eval_operand a t = SOME key /\
  eval_operand b s = SOME x /\ eval_operand b t = SOME y /\
  ~s.vs_call_ctx.cc_static /\ ~t.vs_call_ctx.cc_static /\
  word_agree_except m x y /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL j targets).vs_call_ctx.cc_address = t.vs_call_ctx.cc_address) ==>
  step_inst_base inst s = OK (sstore key x s) /\
  step_inst_base inst t = OK (sstore key y t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (sstore key x s) H)
    (ricf_effective_taint fn (sstore key x s)
      (un with t_stor := key_update un.t_stor key m)) fn
    sites maps targets H (un with t_stor := key_update un.t_stor key m)
    cur curs (sstore key x s) (sstore key y t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, exec_write2_def] >>
  metis_tac[ricf_cert_sstore]
QED

Theorem ricf_cert_step_tstore:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  inst.inst_opcode = TSTORE /\ inst.inst_operands = [a;b] /\
  eval_operand a s = SOME key /\ eval_operand a t = SOME key /\
  eval_operand b s = SOME x /\ eval_operand b t = SOME y /\
  ~s.vs_call_ctx.cc_static /\ ~t.vs_call_ctx.cc_static /\
  word_agree_except m x y /\
  (!j. j < LENGTH stk ==>
    (EL j stk).cf_state.vs_call_ctx.cc_address = s.vs_call_ctx.cc_address /\
    (EL j targets).vs_call_ctx.cc_address = t.vs_call_ctx.cc_address) ==>
  step_inst_base inst s = OK (tstore key x s) /\
  step_inst_base inst t = OK (tstore key y t) /\
  ricf_cert_core D ids stk PG
    (ricf_effective_prov fn (tstore key x s) H)
    (ricf_effective_taint fn (tstore key x s)
      (un with t_trans := key_update un.t_trans key m)) fn
    sites maps targets H (un with t_trans := key_update un.t_trans key m)
    cur curs (tstore key x s) (tstore key y t)
Proof
  strip_tac >> simp[step_inst_base_opcode_eqs, exec_write2_def] >>
  metis_tac[ricf_cert_tstore]
QED

(* Both empty and nonempty gas schedules use the same scalar bind rule.
   The schedule is a shared field, unlike the relocated local variables. *)
Theorem ricf_cert_exec_gas:
  ricf_cert_core D ids stk PG G tn fn sites maps targets H un cur curs s t /\
  inst.inst_outputs = [out] ==>
  ?u v. exec_gas inst s = OK u /\ exec_gas inst t = OK v /\
    ricf_cert_core D ids stk PG
      (ricf_effective_prov fn u (set_prov H [out] NONE))
      (ricf_effective_taint fn u
        (un with t_var := set_var_taint un.t_var [out] {})) fn
      sites maps targets (set_prov H [out] NONE)
      (un with t_var := set_var_taint un.t_var [out] {}) cur curs u v
Proof
  strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
     metis_tac[ricf_frame_effect, ricf_effect_gas_readings]) >>
  pop_assum (mk_asm "schedules") >>
  qpat_x_assum `inst.inst_outputs = [out]` (mk_asm "outputs") >>
  namedCases_on `s.vs_gas_readings` ["", "r rest"]
  >- (qpat_x_assum `s.vs_gas_readings = []` (mk_asm "source") >>
      `t.vs_gas_readings = []` by (asm "schedules" (fn th => metis_tac[th])) >>
      pop_assum (mk_asm "target") >>
      qexistsl [`update_var out 0w s`, `update_var out 0w t`] >>
      asm "outputs" (fn outputs => asm "source" (fn source =>
        asm "target" (fn target =>
          simp_tac std_ss [exec_gas_def, listTheory.list_case_def, outputs, source, target]))) >>
      `ricf_value_agree sites NONE {} 0w 0w` by
        simp[ricf_value_agree_inactive, word_agree_except_def] >>
      metis_tac[ricf_cert_bind, ricf_effective_prov_def, ricf_effective_taint_def]) >>
  qpat_x_assum `s.vs_gas_readings = r::rest` (mk_asm "source") >>
  `t.vs_gas_readings = r::rest` by (asm "schedules" (fn th => metis_tac[th])) >>
  pop_assum (mk_asm "target") >>
  drule ricf_cert_gas_tail >> disch_then (qspec_then `rest` assume_tac) >>
  qexistsl [`update_var out r (s with vs_gas_readings := rest)`,
            `update_var out r (t with vs_gas_readings := rest)`] >>
  asm "outputs" (fn outputs => asm "source" (fn source =>
        asm "target" (fn target =>
          simp_tac std_ss [exec_gas_def, listTheory.list_case_def, outputs, source, target]))) >>
  `ricf_value_agree sites NONE {} r r` by
    simp[ricf_value_agree_inactive, word_agree_except_def] >>
  metis_tac[ricf_cert_bind, ricf_effective_prov_def, ricf_effective_taint_def]
QED
