Theory staticShadowEntry
Ancestors
  staticShadowFrame staticShadowDefs venomState venomExecSemantics
  venomInst list finite_map

Theorem static_shadow_setup_callee:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  setup_callee fn args s = SOME t ==>
  ?th. setup_callee fn args sh = SOME th /\
       static_shadow_rel t th /\ t.vs_call_ctx.cc_static
Proof
  simp[setup_callee_def] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[static_shadow_rel_def, static_shadow_def,
      venom_state_component_equality]
QED

Theorem static_shadow_fold_updates[local]:
  !xs s sh. s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_rel
    (FOLDL (\s (x,v). update_var x v s) s xs)
    (FOLDL (\s (x,v). update_var x v s) sh xs) /\
  (FOLDL (\s (x,v). update_var x v s) s xs).vs_call_ctx.cc_static
Proof
  Induct >> simp[] >> qx_gen_tac `h` >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  simp[] >> first_x_assum irule >>
  simp[static_shadow_rel_update_var, update_var_def]
QED

Theorem static_shadow_bind_outputs:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\
  bind_outputs outs vals s = SOME t ==>
  ?th. bind_outputs outs vals sh = SOME th /\
       static_shadow_rel t th /\ t.vs_call_ctx.cc_static
Proof
  simp[bind_outputs_def] >> strip_tac >>
  gvs[] >> irule static_shadow_fold_updates >> simp[]
QED

Theorem static_shadow_one_phi[local]:
  static_shadow_rel s sh ==> eval_one_phi sh inst = eval_one_phi s inst
Proof
  strip_tac >>
  `sh.vs_prev_bb = s.vs_prev_bb` by
    gvs[static_shadow_rel_def, static_shadow_def,
        venom_state_component_equality] >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  simp[eval_one_phi_def]
QED

Theorem static_shadow_phis:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (eval_phis s insts) (eval_phis sh insts)
Proof
  Induct_on `insts` >- simp[eval_phis_def, static_shadow_result_rel_def] >>
  rpt gen_tac >> strip_tac >>
  `eval_one_phi sh h = eval_one_phi s h` by
    metis_tac[static_shadow_one_phi] >>
  simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[static_shadow_result_rel_def] >>
  Cases_on `eval_one_phi s h` >> simp[static_shadow_result_rel_def] >>
  PairCases_on `x` >> simp[] >>
  first_x_assum drule_all >>
  Cases_on `eval_phis s insts` >>
  simp[static_shadow_result_rel_def] >> strip_tac >>
  simp[static_shadow_rel_update_var] >> simp[update_var_def]
QED
