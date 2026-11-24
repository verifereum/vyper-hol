(* Change only the source scopes at a stationary, nonhalted target cursor. *)
Theory gasExemptScope
Ancestors
  gasExemptCert gasSummary fragGasMode fragGasPathMem vyperState

Theorem gas_exempt_cert_source_scope:
  ~s.vs_halted /\
  (!obs. source (es with gas_obs := obs) =
         scoped ((es with scopes := scopes) with gas_obs := obs)) /\
  gas_exempt_cert T tops (ctx,func) (ignore_bind scoped (return ()))
    (es with scopes := scopes,s) marks (err,ee) (leaf,finish') ==>
  gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
    (es,s) marks (err,ee) (leaf,finish')
Proof
  strip_tac >>
  qabbrev_tac `enter = \src:evaluation_state.
    (if src with gas_obs := [] = es with gas_obs := [] then
       (INL T,src with scopes := scopes)
     else (INL F,src)) : bool evaluation_result` >>
  qabbrev_tac `rest = \b:bool.
    ignore_bind (if b then scoped else source) (return ())` >>
  `vyperState$bind enter rest = ignore_bind source (return ())` by
    (simp[FUN_EQ_THM,Abbr `enter`,Abbr `rest`,bind_def] >>
     gen_tac >> IF_CASES_TAC >> simp[] >>
     `x = es with gas_obs := x.gas_obs` by
       fs[evaluation_state_component_equality] >>
     qpat_assum `x = es with gas_obs := x.gas_obs` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `!obs. source _ = scoped _`
       (qspec_then `x.gas_obs` mp_tac) >>
     simp[ignore_bind_def,bind_def,evaluation_state_component_equality]) >>
  `gas_marked_exec T (ctx,func) enter (es,s) [] (INL T)
       (es with scopes := scopes) (OK s)` by
    (simp[gas_marked_exec_def,gas_explicit_def,Abbr `enter`,
          evaluation_state_component_equality] >>
     irule gas_marked_path_from_mem >> simp[cj 1 gas_path_mem_rules]) >>
  `gas_exempt_cert T tops (ctx,func) (rest T)
    ((es with scopes := scopes) with gas_obs := [],s)
    marks (err,ee) (leaf,finish')` by
    (simp[Abbr `rest`] >> drule gas_exempt_cert_start_gas_obs >> simp[]) >>
  drule_all gas_exempt_cert_bind_bool >> simp[]
QED
