Theory algebraicOptCmpStepProofs
Ancestors
  algebraicOptCmpSimulationProofs algebraicOptCmpCallProofs
  execEquivParamProofs execEquivParamProps instIdxIndep venomInstProps venomExecProps
  stateEquiv stateFrame venomState venomExecSemantics pred_set

Theorem ao_cmp_state_rel_forget:
  !ignored flipped s t.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\
    s.vs_prev_bb = t.vs_prev_bb ==>
    state_equiv (ignored UNION flipped) (s with vs_inst_idx := 0)
      (t with vs_inst_idx := 0)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_state_rel_def]) >>
  simp_tac std_ss [state_equiv_def, execution_equiv_def,
    execution_frame_updates, lookup_var_def,
    venom_state_accfupds, IN_UNION] >>
  metis_tac[lookup_var_def]
QED

Theorem ao_cmp_state_rel_recover:
  !ignored flipped s t u v.
    ao_cmp_state_rel ignored flipped s t /\
    execution_equiv (ignored UNION flipped) u v /\
    (!x. x IN flipped /\ x NOTIN ignored ==>
      lookup_var x u = lookup_var x s /\
      lookup_var x v = lookup_var x t) ==>
    ao_cmp_state_rel ignored flipped u v
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_state_rel_def]) >>
  qpat_x_assum `execution_equiv _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [execution_equiv_def]) >>
  pure_rewrite_tac[ao_cmp_state_rel_def] >>
  conj_tac >- asm_rewrite_tac[] >>
  rpt strip_tac >> Cases_on `v' IN flipped` >>
  metis_tac[IN_UNION]
QED

Theorem ao_cmp_step_base_idx_norm[local]:
  !inst s.
    exec_result_map (\u. u with vs_inst_idx := 0)
      (step_inst_base inst (s with vs_inst_idx := 0)) =
    exec_result_map (\u. u with vs_inst_idx := 0) (step_inst_base inst s)
Proof
  rpt gen_tac >> Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[terminator_step_inst_base_idx_norm0] >>
  drule step_inst_inst_idx_indep >>
  disch_then (qspecl_then [`s`, `0`] assume_tac) >>
  asm_rewrite_tac[] >> Cases_on `step_inst_base inst s` >>
  simp[exec_result_map_def]
QED

Theorem ao_cmp_step_non_invoke:
  !ignored flipped fuel ctx inst s t.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    (!x. MEM (Var x) inst.inst_operands ==>
      x NOTIN ignored /\ x NOTIN flipped) /\
    EVERY (\x. x NOTIN flipped) inst.inst_outputs /\
    inst.inst_opcode <> INVOKE ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (\u v. ao_cmp_state_rel ignored flipped u v /\
      u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
Proof
  rpt gen_tac >> strip_tac >>
  `state_equiv (ignored UNION flipped) (s with vs_inst_idx := 0)
     (t with vs_inst_idx := 0)` by
    (irule ao_cmp_state_rel_forget >> simp[]) >>
  `lift_result (state_equiv (ignored UNION flipped))
     (execution_equiv UNIV) (execution_equiv UNIV)
     (step_inst fuel ctx inst (s with vs_inst_idx := 0))
     (step_inst fuel ctx inst (t with vs_inst_idx := 0))` by
    (`valid_state_rel (state_equiv (ignored UNION flipped))
        (execution_equiv UNIV)` by
       (irule valid_state_rel_mixed >> simp[]) >>
     irule step_inst_preserves_R >> asm_rewrite_tac[] >>
     rpt strip_tac >>
     qpat_x_assum `state_equiv _ _ _` mp_tac >>
     simp_tac std_ss [state_equiv_def, execution_equiv_def, lookup_var_def,
       venom_state_accfupds, IN_UNION] >> metis_tac[]) >>
  `lift_result (state_equiv (ignored UNION flipped))
     (execution_equiv UNIV) (execution_equiv UNIV)
     (exec_result_map (\u. u with vs_inst_idx := 0) (step_inst_base inst s))
     (exec_result_map (\u. u with vs_inst_idx := 0) (step_inst_base inst t))` by
    (once_rewrite_tac[GSYM ao_cmp_step_base_idx_norm] >>
     qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
     asm_simp_tac std_ss [step_inst_non_invoke] >>
     Cases_on `step_inst_base inst (s with vs_inst_idx := 0)` >>
     Cases_on `step_inst_base inst (t with vs_inst_idx := 0)` >>
     simp_tac std_ss [lift_result_def, exec_result_map_def,
       state_equiv_def, execution_equiv_def, execution_frame_updates,
       lookup_var_def, venom_state_accfupds]) >>
  qpat_x_assum `lift_result _ _ _ (exec_result_map _ _) _` mp_tac >>
  qpat_x_assum `lift_result _ _ _ _ _` kall_tac >>
  asm_simp_tac std_ss [step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> Cases_on `step_inst_base inst t` >>
  simp_tac std_ss [exec_result_map_def, lift_result_def,
    state_equiv_def, execution_equiv_def, execution_frame_updates,
    lookup_var_def, venom_state_accfupds] >>
  rpt strip_tac >> disj2_tac >>
  irule ao_cmp_state_rel_recover >>
  conj_tac >- (simp_tac std_ss [execution_equiv_def, lookup_var_def] >>
               asm_rewrite_tac[]) >>
  qexistsl_tac [`s`, `t`] >> asm_rewrite_tac[] >>
  rpt gen_tac >> strip_tac >>
  `step_inst fuel ctx inst s = OK v /\ step_inst fuel ctx inst t = OK v'` by
    simp[step_inst_non_invoke] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_terminator_preserves_vars] >>
  `~MEM x inst.inst_outputs` by
    (qpat_x_assum `EVERY _ _` mp_tac >>
     simp_tac std_ss [listTheory.EVERY_MEM] >> metis_tac[]) >>
  metis_tac[venomInstPropsTheory.step_preserves_non_output_vars]
QED

Theorem ao_cmp_step:
  !ignored flipped fuel ctx inst s t.
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    (!x. MEM (Var x) inst.inst_operands ==>
      x NOTIN ignored /\ x NOTIN flipped) /\
    EVERY (\x. x NOTIN flipped) inst.inst_outputs ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (\u v. ao_cmp_state_rel ignored flipped u v /\
      u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (`lift_result (ao_cmp_state_rel ignored flipped)
         (execution_equiv UNIV) (execution_equiv UNIV)
         (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)` by
        (irule ao_cmp_invoke >> asm_rewrite_tac[] >>
         rpt strip_tac >>
         `!op. MEM op ops ==> eval_operand op s = eval_operand op t` by
           (rpt strip_tac >> irule ao_cmp_state_rel_operand >>
            asm_rewrite_tac[] >> rpt strip_tac >>
            `!x. MEM (Var x) ops ==> MEM (Var x) inst.inst_operands` by
              (gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[listTheory.MEM]) >>
            metis_tac[]) >>
         qpat_x_assum `decode_invoke _ = _` kall_tac >>
         Induct_on `ops` >> simp[eval_operands_def]) >>
      Cases_on `step_inst fuel ctx inst s` >>
      Cases_on `step_inst fuel ctx inst t` >>
      gvs[lift_result_def] >>
      metis_tac[step_preserves_control_flow, venomInstTheory.is_terminator_def]) >>
  irule ao_cmp_step_non_invoke >> simp[]
QED
