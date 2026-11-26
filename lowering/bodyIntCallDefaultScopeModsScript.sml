Theory bodyIntCallDefaultScopeMods
Ancestors
  bodyFullIntCallArgs vyperInterpreter vyperState vyperTypeSystem
  pair sum list finite_map

(* Changing the ambient scopes is invisible to a supported, well-typed
   default slice; only the final state's scopes follow the change. *)
Theorem intcall_default_slice_scope_mods:
  supported_pure_exprs tops xs /\ well_typed_exprs (defaults_env tenv) xs ==>
  !p z sc. eval_exprs p xs (z with scopes := sc) =
    (FST (eval_exprs p xs z), SND (eval_exprs p xs z) with scopes := sc)
Proof
  strip_tac >> mp_tac (cj 2 intcall_args_defaults_scope_mutual_from_actions) >>
  simp[intcall_args_conditional_result_scope_action,
       intcall_args_conditional_result_nonlocal,
       intcall_args_result_array_length_scope_action,
       intcall_args_select_result_scope_action,
       intcall_args_select_result_nonlocal] >>
  (impl_tac >- (conj_tac
    >- metis_tac[intcall_args_conditional_result_nonlocal] >>
    metis_tac[intcall_args_select_result_nonlocal])) >>
  disch_then (qspecl_then [`tops`,`xs`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `!tenv. well_typed_exprs _ _ ==> _`
    (drule_all_then ACCEPT_TAC)
QED

Theorem intcall_default_slice_bracket_mods:
  supported_pure_exprs tops xs /\ well_typed_exprs (defaults_env tenv) xs ==>
  !p z. finally (ignore_bind (set_scopes [FEMPTY]) (eval_exprs p xs))
          (set_scopes z.scopes) z = eval_exprs p xs z
Proof
  rpt strip_tac >>
  drule_all_then (qspecl_then [`p`,`z`] assume_tac) intcall_default_slice_scope_mods >>
  `eval_exprs p xs (z with scopes := [FEMPTY]) =
   (FST (eval_exprs p xs z), SND (eval_exprs p xs z) with scopes := [FEMPTY])` by simp[] >>
  Cases_on `eval_exprs p xs z` >>
  rename1 `eval_exprs p xs z = (res,fin)` >>
  `fin.scopes = z.scopes` by
    (qpat_x_assum `!sc. _` (qspec_then `z.scopes` mp_tac) >> simp[] >>
     disch_then (mp_tac o AP_TERM ``\s:evaluation_state. s.scopes``) >> simp[]) >>
  `fin with scopes := z.scopes = fin` by
    (qpat_assum `fin.scopes = _` (SUBST1_TAC o SYM) >> simp[]) >>
  Cases_on `res` >>
  simp[finally_def, ignore_bind_apply, set_scopes_def, return_def, raise_def]
QED
