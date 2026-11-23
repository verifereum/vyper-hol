(* Checked linked runtime entry preserves the source machine's immutable store. *)
Theory vyperLinkedRuntimeImmutables
Ancestors
  alist finite_map vyperState vyperContext vyperInterpreter vyperTypeContract
  vyperTypeCallGraph vyperTypeSelectedEntry vyperSelectedRuntimeLiveCalls
  vyperRuntimeWriteSafety vyperCheckedRuntimeWriteSafety
  vyperLiveRuntimeCallableGuards vyperLiveRuntimeEntryFrame vyperRuntimeCallFrame

Theorem call_external_runtime_mods_preserves_immutables:
  check_contract F am.layouts tx.target mods = SOME art /\
  exports_ok am.layouts tx.target mods exps /\
  ALOOKUP am.sources tx.target = SOME mods /\
  (ALOOKUP am.exports tx.target = SOME exps \/
   exps = [] /\ ALOOKUP am.exports tx.target = NONE) /\
  call_external orc gobs am tx = (res, am', rqs) ==>
  am'.immutables = am.immutables
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse (Cases_on `?ms sel. selected_entry am tx ms sel`)
  >- (drule call_external_not_selected_entry >>
      disch_then (qspecl_then [`orc`,`gobs`] strip_assume_tac) >> gvs[]) >>
  gvs[selected_entry_def] >>
  PairCases_on `sel` >>
  qabbrev_tac `src = find_function_module am tx.target tx.function_name` >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx src` >>
  rename1 `lookup_exported_function cx am tx.function_name = SOME (mut,nr,args,ds,rt,b)` >>
  `selected_entry am tx mods (mut,nr,args,ds,rt,b)` by
    simp[selected_entry_def, Abbr `cx`, Abbr `src`] >>
  `?ts. get_module_code cx src = SOME ts /\ ALOOKUP mods src = SOME ts` by
    (simp[Abbr `cx`, Abbr `src`] >> metis_tac[selected_entry_module_code]) >>
  `module_allocated am.layouts tx.target src ts /\
   EVERY (\k. MEM k (live_functions am.layouts tx.target mods))
      (function_int_calls ds b)` by
    (unabbrev_all_tac >> metis_tac[selected_runtime_entry_live_calls]) >>
  qabbrev_tac `P = \k. MEM k (live_functions am.layouts tx.target mods)` >>
  qabbrev_tac `R = \sid id. ?vt. FLOOKUP art.cta_toplevel_vtypes (sid,id) = SOME vt /\
                               FLOOKUP art.cta_bare_globals (sid,id) = NONE` >>
  `runtime_write_roots_resolve cx R` by
    (simp[runtime_write_roots_resolve_def, Abbr `R`, Abbr `cx`] >>
     metis_tac[checked_runtime_write_roots]) >>
  `EVERY (expr_writes_ok (runtime_write_root R)) ds /\
   stmts_writes_ok (runtime_write_root R) b` by
    (irule checked_external_selected_writes >> simp[Abbr `R`] >>
     metis_tac[markerTheory.Abbrev_def]) >>
  `!sid fn ts' mut' nr' args' ds' rt' b'.
     P (sid,fn) /\ get_module_code cx sid = SOME ts' /\
     lookup_callable_function F fn ts' = SOME (mut',nr',args',ds',rt',b') ==>
     EVERY (expr_writes_ok (runtime_write_root R)) ds' /\
     stmts_writes_ok (runtime_write_root R) b' /\ EVERY P (function_int_calls ds' b')` by
    (simp[Abbr `P`, Abbr `R`, Abbr `cx`, initial_evaluation_context_def, get_module_code_def] >>
     metis_tac[checked_live_runtime_callable_guards]) >>
  `~cx.in_deploy` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  `EVERY P (function_int_calls ds b)` by simp[Abbr `P`] >>
  drule_all live_runtime_entry_immutable_frames >> strip_tac >>
  qpat_x_assum `call_external _ _ _ _ = _` mp_tac >>
  fs[markerTheory.Abbrev_def] >>
  drule_all call_external_selected_entry >> disch_then (fn th => simp[th]) >>
  Cases_on `call_external_function orc gobs am cx nr mut ts mods args ds tx.args b rt` >>
  rename1 `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = outcome` >>
  PairCases_on `outcome` >>
  rename1 `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = (out,am1,requests)` >>
  `am1.immutables = am.immutables` by metis_tac[call_external_function_runtime_frame] >>
  Cases_on `out` >> gvs[AllCaseEqs()] >> strip_tac >> gvs[]
QED
