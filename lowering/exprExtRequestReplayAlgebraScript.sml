Theory exprExtRequestReplayAlgebra
Ancestors exprExtRequestStagesSource vyperInterpreter vyperState list

Definition extrequest_success_replay_def:
  extrequest_success_replay f <=>
    !s x t. f s = (INL x,t) ==> ?used. !tail.
      f (s with gas_obs := used ++ tail) =
        (INL x,t with gas_obs := tail)
End

Definition extrequest_obs_equivariant_def:
  extrequest_obs_equivariant f <=>
    !s tail. f (s with gas_obs := tail) =
      let (res,t) = f s in (res,t with gas_obs := tail)
End

Theorem extrequest_equivariant_replay:
  extrequest_obs_equivariant f ==> extrequest_success_replay f
Proof
  rw[extrequest_obs_equivariant_def, extrequest_success_replay_def] >>
  qexists `[]` >> simp[]
QED

Theorem extrequest_replay_return:
  extrequest_success_replay (return x)
Proof
  simp[extrequest_success_replay_def, return_def] >> rpt strip_tac >>
  qexists `[]` >> simp[]
QED

Theorem extrequest_replay_raise:
  extrequest_success_replay (raise e)
Proof
  simp[extrequest_success_replay_def, raise_def]
QED

Theorem extrequest_replay_bind:
  extrequest_success_replay f /\
  (!x. extrequest_success_replay (g x)) ==>
  extrequest_success_replay (bind f g)
Proof
  simp[extrequest_success_replay_def] >> rpt strip_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  rename1 `f s = (INL a,m)` >>
  qpat_x_assum `!s x t. f s = _ ==> _` drule >>
  disch_then (qx_choose_then `used` assume_tac) >>
  qpat_x_assum `!x s x' t. _` (qspec_then `a` mp_tac) >>
  disch_then drule >>
  disch_then (qx_choose_then `more` assume_tac) >>
  qexists `used ++ more` >> gen_tac >>
  qpat_assum `!tail. f _ = _` (qspec_then `more ++ tail` assume_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[bind_def, Excl "APPEND_ASSOC"]
QED

Theorem extrequest_replay_gas_read:
  extrequest_success_replay next_gas_reading
Proof
  rw[extrequest_success_replay_def] >>
  `next_gas_reading (s with gas_obs := s.gas_obs) = (INL x,t)` by simp[] >>
  drule extrequest_gas_read_replay_probe >> strip_tac >>
  qexists `[w]` >> simp[]
QED
