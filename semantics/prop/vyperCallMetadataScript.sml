(* Runtime external calls retain the module sources and storage layouts. *)
Theory vyperCallMetadata
Ancestors
  vyperInterpreter vyperState vyperContext vyperValue list pair

Theorem call_external_function_nondeploy_metadata:
  ~cx.in_deploy /\
  call_external_function orc gobs am cx nr mut ts all_mods args dflts vals body ret =
    (res,am',rqs) ==>
  am'.sources = am.sources /\ am'.layouts = am.layouts
Proof
  strip_tac >>
  fs[call_external_function_def, call_external_function_trace_def, AllCaseEqs(),
     Excl "lock_if_nr_def", Excl "unlock_if_nr_def", Excl "is_view_mut_def"] >>
  gvs[abstract_machine_from_state_def] >>
  pairarg_tac >>
  gvs[AllCaseEqs(), abstract_machine_from_state_def]
QED

Theorem call_external_metadata:
  !orc gobs am tx res am' rqs.
    call_external orc gobs am tx = (res,am',rqs) ==>
    am'.sources = am.sources /\ am'.layouts = am.layouts
Proof
  rpt gen_tac >>
  `!cx nr mut (ts : toplevel list) all_mods args dflts vals body ret result am_out requests obs.
     call_external_function_trace orc gobs am cx nr mut ts all_mods args dflts vals body ret =
       (result,am_out,requests,obs) ==> ~cx.in_deploy ==>
     am_out.sources = am.sources /\ am_out.layouts = am.layouts` by
    (rpt gen_tac >> disch_tac >> disch_tac >>
     `call_external_function orc gobs am cx nr mut ts all_mods args dflts vals body ret =
        (result,am_out,requests)` by simp[call_external_function_def] >>
     drule_all call_external_function_nondeploy_metadata >> simp[]) >>
  pure_rewrite_tac[call_external_def, call_external_trace_def, LET_THM] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >>
  simp[initial_evaluation_context_def]
QED
