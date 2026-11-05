(* Return-local restoration, independent of historical caller shared state. *)
Theory o1LowerDloadRestore
Ancestors
  o1LowerDloadEnvironment o1LowerDloadRelocationKernel ptrDiscipline
  venomExecSemantics venomInstProofs1 venomState unitShapeDefs irSupply
  finite_map list pred_set option

Theorem ld_env_merge:
  ld_env_agree sites fn H tn caller caller' ==>
  ld_env_agree sites fn H tn (merge_callee_state caller callee)
    (merge_callee_state caller' callee')
Proof
  simp[ld_env_agree_def, merge_callee_state_def]
QED

Theorem ld_params_merge:
  ld_params_agree sites HP caller caller' ==>
  ld_params_agree sites HP (merge_callee_state caller callee)
    (merge_callee_state caller' callee')
Proof
  simp[ld_params_agree_def, merge_callee_state_def]
QED

Theorem ld_env_bind_one[local]:
  ld_env_agree sites fn H tn s t ==>
  ld_env_agree sites fn (DRESTRICT H (COMPL {out}))
    (tn with t_var := DRESTRICT tn.t_var (COMPL {out}))
    (update_var out value s) (update_var out value t)
Proof
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def] >> rpt strip_tac >>
  Cases_on `v = out` >> gvs[ld_value_agree_scalar, word_agree_except_def] >>
  metis_tac[]
QED

Theorem ld_bind_cons[local]:
  bind_outputs (out::outs) (value::vals) s =
  bind_outputs outs vals (update_var out value s)
Proof
  simp[bind_outputs_def]
QED

Theorem ld_env_bind_outputs:
  !outs vals s t H tn s1.
  ld_env_agree sites fn H tn s t /\ bind_outputs outs vals s = SOME s1 ==>
  ?t1. bind_outputs outs vals t = SOME t1 /\
    ld_env_agree sites fn (DRESTRICT H (COMPL (set outs)))
      (tn with t_var := DRESTRICT tn.t_var (COMPL (set outs))) s1 t1
Proof
  Induct
  >- (Cases_on `vals` >> simp[bind_outputs_def, DRESTRICT_UNIV]) >>
  Cases_on `vals` >- simp[bind_outputs_def] >>
  pure_rewrite_tac[ld_bind_cons] >> rpt strip_tac >>
  rename1 `bind_outputs outs vals (update_var out value s) = SOME s1` >>
  rename1 `ld_env_agree sites fn H tn s target` >>
  `ld_env_agree sites fn (DRESTRICT H (COMPL {out}))
     (tn with t_var := DRESTRICT tn.t_var (COMPL {out}))
     (update_var out value s) (update_var out value target)` by
    (irule ld_env_bind_one >> simp[]) >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  `COMPL {out} INTER COMPL (set outs) = COMPL (out INSERT set outs)` by simp[EXTENSION] >>
  qexists_tac `t1` >> gvs[DRESTRICT_DRESTRICT, INTER_COMM]
QED

Theorem ld_params_bind_outputs:
  bind_outputs outs vals s = SOME s1 /\ bind_outputs outs vals t = SOME t1 /\
  ld_params_agree sites HP s t ==> ld_params_agree sites HP s1 t1
Proof
  strip_tac >>
  `s1.vs_params = s.vs_params` by
    (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
  `t1.vs_params = t.vs_params` by
    (irule bind_outputs_preserves >> simp[update_var_def] >> metis_tac[]) >>
  gvs[ld_params_agree_def]
QED

Theorem ld_return_local_restore:
  ld_env_agree sites fn H tn caller caller' /\
  ld_params_agree sites HP caller caller' /\
  bind_outputs outs vals (merge_callee_state caller callee) = SOME s1 ==>
  ?t1. bind_outputs outs vals (merge_callee_state caller' callee') = SOME t1 /\
    ld_env_agree sites fn (DRESTRICT H (COMPL (set outs)))
      (tn with t_var := DRESTRICT tn.t_var (COMPL (set outs))) s1 t1 /\
    ld_params_agree sites HP s1 t1
Proof
  strip_tac >>
  `ld_env_agree sites fn H tn (merge_callee_state caller callee)
     (merge_callee_state caller' callee')` by (irule ld_env_merge >> simp[]) >>
  drule_all ld_env_bind_outputs >> strip_tac >>
  qexists_tac `t1` >> simp[] >> irule ld_params_bind_outputs >>
  goal_assum drule >> goal_assum drule >> irule ld_params_merge >> simp[]
QED
