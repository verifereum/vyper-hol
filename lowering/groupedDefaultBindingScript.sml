Theory groupedDefaultBinding
Ancestors externalEntryBound vyperInterpreter vyperState

Theorem grouped_defaults_bound_frame:
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [FEMPTY] with <|outcomes := SOME os; requests := []|>) =
    (INL (), s1) /\
  (!tail. eval_exprs (initial_evaluation_context am.sources am.layouts tx NONE)
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
    (s1 with gas_obs := prefix ++ tail) = (INL values, es with gas_obs := tail)) /\
  es with gas_obs := [] = s1 with gas_obs := [] /\
  bind_arguments (type_env tops) args (tx.args ++ values) = SOME env ==>
  (!tail. external_entry_bound tops am tx os (prefix ++ tail) mut args dflts
    (es with <|scopes := [env]; gas_obs := tail|>)) /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with <|outcomes := SOME os; requests := []|>) =
    (INL (), es with <|scopes := [env]; gas_obs := []|>)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule send_call_value_with_scopes >> simp[initial_state_def] >> strip_tac >>
  conj_tac
  >- (gen_tac >>
      qpat_assum `!tail. eval_exprs _ _ _ = _`
        (qspec_then `tail` assume_tac) >>
      irule external_entry_bound_from_default_evaluation >>
      qexistsl_tac [`s1`,`values`] >> asm_rewrite_tac[]) >>
  `s1.gas_obs = []` by
    (drule send_call_value_with_gas_obs >> simp[initial_state_def]) >>
  qpat_assum `es with gas_obs := [] = s1 with gas_obs := []`
    (fn th => mp_tac (AP_TERM (Parse.Term `\e. e with scopes := [env]`) th)) >>
  BETA_TAC >> simp[evaluation_state_component_equality]
QED
