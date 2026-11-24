Theory linkedRuntimeSelectedTrace
Ancestors vyperInterpreter vyperContext vyperState vyperCall arithmetic list option pair

Theorem linked_runtime_selected_trace:
  ALOOKUP am.sources tx.target = SOME mods /\
  find_function_module am tx.target tx.function_name = src /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  get_module_code cx src = SOME tops /\
  lookup_exported_function cx am tx.function_name = SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  send_call_value mut cx
    (initial_state am [FEMPTY] with
       <|outcomes := SOME os; requests := []; gas_obs := gobs; storage_trace := []|>) =
    (INL (),paid) /\
  eval_external_defaults cx (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts)
    paid = (INL defaults,after_defaults) /\
  bind_arguments (type_env_all_modules mods) args (tx.args ++ defaults) = SOME env /\
  lock_if_nr cx nr (is_view_mut mut) (after_defaults with scopes := [env]) =
    (INL (),locked) /\
  eval_stmts cx body locked = (res,ee) /\
  unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),unlocked) ==>
  ?r am' rqs obs.
    call_external_trace (SOME os) gobs am tx = (r,am',rqs,obs) /\
    ((res = INL () \/ (?v. res = INR (ReturnException v))) ==>
      obs = unlocked.storage_trace) /\
    (~(res = INL () \/ (?v. res = INR (ReturnException v))) ==>
      obs = ee.storage_trace) /\
    (res = INL () ==>
      r = INL NoneV /\ rqs = unlocked.requests /\
      am' = finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts unlocked)) /\
    (!v. res = INR (ReturnException v) ==>
      rqs = unlocked.requests /\
      (r,am') =
        case evaluate_type (type_env_all_modules mods) ret of
          NONE => (INR (Error (TypeError "eval ret")),am)
        | SOME tv =>
            case safe_cast tv v of
              NONE => (INR (Error (TypeError "ext cast ret")),am)
            | SOME v' => (INL v',finalize_pending_deletions
                (abstract_machine_from_state am.sources am.exports am.layouts unlocked))) /\
    (res = INR HaltException ==>
      r = INR HaltException /\ rqs = ee.requests /\
      am' = finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts ee)) /\
    (!e. res = INR e /\ (!v. e <> ReturnException v) /\ e <> HaltException ==>
      r = INR e /\ am' = am /\ rqs = ee.requests)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~cx.in_deploy` by
    (qpat_assum `cx = initial_evaluation_context _ _ _ _` SUBST1_TAC >>
     simp[NoAsms, initial_evaluation_context_def]) >>
  `(case src of NONE => get_self_code cx
                | SOME src_id => get_module_code cx (SOME src_id)) = SOME tops` by
    (Cases_on `src` >> simp[NoAsms, get_self_code_def] >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `cx = initial_evaluation_context _ _ _ _` (fn cx =>
    qpat_assum `find_function_module am tx.target tx.function_name = src` (fn selected =>
      PURE_REWRITE_TAC [call_external_trace_def, LET_THM] >>
      BETA_TAC >>
      PURE_REWRITE_TAC [selected, GSYM cx])) >>
  `~(LENGTH tx.args > LENGTH args \/
      LENGTH args - LENGTH tx.args > LENGTH dflts)` by decide_tac >>
  asm_simp_tac (srw_ss()) [] >>
  PURE_REWRITE_TAC [call_external_function_trace_def, LET_THM] >>
  asm_simp_tac std_ss [] >>
  asm_simp_tac std_ss [bind_def, ignore_bind_def, set_scopes_def,
    return_def, optionTheory.option_case_def, sumTheory.sum_case_def,
    pairTheory.pair_case_thm, pairTheory.UNCURRY] >>
  namedCases_on `res` ["u","exc"]
  >- (Cases_on `u` >> asm_simp_tac (srw_ss()) []) >>
  Cases_on `exc` >> asm_simp_tac (srw_ss()) [] >>
  Cases_on `evaluate_type (type_env_all_modules mods) ret` >>
  asm_simp_tac (srw_ss()) [] >>
  rename1 `evaluate_type (type_env_all_modules mods) ret = SOME tv` >>
  rename1 `eval_stmts cx body locked = (INR (ReturnException value),ee)` >>
  Cases_on `safe_cast tv value` >> asm_simp_tac (srw_ss()) []
QED
