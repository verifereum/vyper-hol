Theory algebraicOptCmpCallProofs
Ancestors
  algebraicOptCmpSimulationProofs stateFrame venomState venomExecSemantics
  list stateEquiv stateEquivProps

Theorem ao_cmp_setup_callee:
  ao_cmp_state_rel ignored flipped s t ==>
  setup_callee fn args s = setup_callee fn args t
Proof
  strip_tac >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_state_rel_def]) >>
  qpat_x_assum `execution_frame _ = _` mp_tac >>
  rewrite_tac[execution_frame_eq_reconstruct] >>
  disch_then (SUBST1_TAC o SYM) >> simp[setup_callee_def]
QED

Theorem ao_cmp_merge_callee:
  ao_cmp_state_rel ignored flipped s t ==>
  ao_cmp_state_rel ignored flipped
    (merge_callee_state s callee) (merge_callee_state t callee)
Proof
  strip_tac >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_state_rel_def]) >>
  pure_rewrite_tac[ao_cmp_state_rel_def] >> conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      rewrite_tac[execution_frame_eq_reconstruct] >>
      disch_then (SUBST1_TAC o SYM) >>
      simp[merge_callee_state_def, execution_frame_def]) >>
  simp[lookup_var_def, merge_callee_state_def] >>
  metis_tac[lookup_var_def]
QED

Theorem ao_cmp_adopt_return:
  ao_cmp_state_rel ignored flipped s t ==>
  ao_cmp_state_rel ignored flipped (adopt_return_fmp ir s) (adopt_return_fmp ir t)
Proof
  strip_tac >> Cases_on `ir.iret_adopt_fmp`
  >- simp[adopt_return_fmp_def] >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [ao_cmp_state_rel_def]) >>
  pure_rewrite_tac[ao_cmp_state_rel_def] >> conj_tac
  >- (qpat_x_assum `execution_frame _ = _` mp_tac >>
      rewrite_tac[execution_frame_eq_reconstruct] >>
      disch_then (SUBST1_TAC o SYM) >>
      simp[adopt_return_fmp_def, execution_frame_def]) >>
  simp[lookup_var_def, adopt_return_fmp_def] >>
  metis_tac[lookup_var_def]
QED

Theorem ao_cmp_bind_fold[local]:
  !outs vals s t.
    LENGTH outs = LENGTH vals /\ EVERY (\v. v NOTIN flipped) outs /\
    ao_cmp_state_rel ignored flipped s t ==>
    ao_cmp_state_rel ignored flipped
      (FOLDL (\s (out,value). update_var out value s) s (ZIP (outs,vals)))
      (FOLDL (\s (out,value). update_var out value s) t (ZIP (outs,vals)))
Proof
  Induct >> Cases_on `vals` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  irule ao_cmp_state_rel_write >> simp[]
QED

Theorem ao_cmp_bind_outputs:
  ao_cmp_state_rel ignored flipped s t /\
  EVERY (\v. v NOTIN flipped) outs ==>
  OPTREL (ao_cmp_state_rel ignored flipped)
    (bind_outputs outs vals s) (bind_outputs outs vals t)
Proof
  strip_tac >> simp[bind_outputs_def] >> IF_CASES_TAC >> simp[] >>
  irule ao_cmp_bind_fold >> simp[]
QED

Theorem ao_cmp_invoke:
  ao_cmp_state_rel ignored flipped s t /\ inst.inst_opcode = INVOKE /\
  EVERY (\v. v NOTIN flipped) inst.inst_outputs /\
  (!name ops. decode_invoke inst = SOME (name,ops) ==>
     eval_operands ops s = eval_operands ops t) ==>
  lift_result (ao_cmp_state_rel ignored flipped)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
Proof
  strip_tac >> Cases_on `decode_invoke inst`
  >- simp[step_inst_def, lift_result_def] >>
  rename1 `decode_invoke inst = SOME decoded` >> PairCases_on `decoded` >>
  `eval_operands decoded1 s = eval_operands decoded1 t` by metis_tac[] >>
  Cases_on `lookup_function decoded0 ctx.ctx_functions`
  >- simp[step_inst_def, lift_result_def] >>
  rename1 `lookup_function decoded0 ctx.ctx_functions = SOME fn` >>
  Cases_on `eval_operands decoded1 s`
  >- (gvs[] >> simp[step_inst_def, lift_result_def]) >>
  rename1 `eval_operands decoded1 s = SOME args` >>
  qpat_x_assum `SOME args = eval_operands decoded1 t` (assume_tac o SYM) >>
  `setup_callee fn args s = setup_callee fn args t` by
    (irule ao_cmp_setup_callee >> metis_tac[]) >>
  Cases_on `setup_callee fn args s` >>
  qpat_x_assum `_ = setup_callee fn args t` (assume_tac o SYM)
  >- simp[step_inst_def, lift_result_def] >>
  rename1 `setup_callee fn args s = SOME callee` >>
  Cases_on `run_blocks fuel ctx fn callee` >>
  asm_rewrite_tac[step_inst_def] >>
  simp[lift_result_def, execution_equiv_refl] >>
  drule ao_cmp_merge_callee >>
  disch_then (qspec_then `v` assume_tac) >>
  drule ao_cmp_adopt_return >>
  disch_then (qspec_then `i` assume_tac) >>
  drule_all ao_cmp_bind_outputs >>
  disch_then (qspec_then `i.iret_values` mp_tac) >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state t v))` >>
  simp[lift_result_def]
QED
