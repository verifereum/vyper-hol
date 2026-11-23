Theory groupedDefaultBinding
Ancestors externalEntryBound vyperInterpreter vyperState vyperContext e2eDefs arithmetic pair

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

Theorem grouped_default_initializer_exception_trace:
  source_deployment_rel tops am tx /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  LENGTH tx.args <= LENGTH args /\ LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with <|outcomes := SOME os; requests := []|>) =
    (INL (),es) /\ es.scopes = [FEMPTY] /\
  (!tail. eval_exprs cx
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
    (es with gas_obs := prefix ++ tail) = (INR ex,ee with gas_obs := tail)) /\
  (!v. ex <> ReturnException v) ==>
  !tail. call_external_trace (SOME os) (prefix ++ tail) am tx =
    (INR ex,
     if ex = HaltException then finalize_pending_deletions
       (abstract_machine_from_state am.sources am.exports am.layouts ee)
     else am,ee.requests,ee.storage_trace)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qx_gen_tac `tail` >>
  drule send_call_value_with_gas_obs >> strip_tac >>
  qpat_assum `!gs. send_call_value _ _ _ = _`
    (qspec_then `prefix ++ tail` assume_tac) >>
  qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `tail` assume_tac) >>
  qpat_x_assum `source_deployment_rel tops am tx`
    (strip_assume_tac o REWRITE_RULE [source_deployment_rel_def]) >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  `call_external_function_trace (SOME os) (prefix ++ tail) am
    (initial_evaluation_context am.sources am.layouts tx NONE)
    nr mut tops [(NONE,tops)] args dflts tx.args fbody ret =
    (INR ex,
     if ex = HaltException then abstract_machine_from_state am.sources am.exports am.layouts ee
     else am,ee.requests,ee.storage_trace)` by
    (qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
     `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
     `~(LENGTH args < LENGTH tx.args) /\
      ~(LENGTH dflts < LENGTH args - LENGTH tx.args)` by decide_tac >>
     `(es with gas_obs := prefix ++ tail) with scopes := [FEMPTY] =
       es with gas_obs := prefix ++ tail` by simp[evaluation_state_component_equality] >>
     `(ee with gas_obs := tail).requests = ee.requests /\
      (ee with gas_obs := tail).storage_trace = ee.storage_trace` by simp[] >>
     `abstract_machine_from_state am.sources am.exports am.layouts
        (ee with <|gas_obs := tail; scopes := es.scopes|>) =
       abstract_machine_from_state am.sources am.exports am.layouts ee` by
       simp[abstract_machine_from_state_def] >>
     simp_tac bool_ss [call_external_function_trace_def, LET_THM] >>
     asm_rewrite_tac[ignore_bind_def, bind_def, initial_state_def,
       evaluation_state_accfupds] >>
     Cases_on `ex` >> fs[eval_external_defaults_run, pairTheory.UNCURRY,
       abstract_machine_from_state_def, initial_state_def, evaluation_state_accfupds]) >>
  Cases_on `ex` >>
  fs[call_external_trace_def, find_function_module_def,
    lookup_exported_function_def, get_self_code_def, get_module_code_def,
    initial_evaluation_context_def, pairTheory.UNCURRY] >>
  metis_tac[]
QED
