(* Constructor-sensitive result interface for free-memory-pointer transport.
 * Continuing results retain the caller's call-entry pointer replacement;
 * terminal results may instead retain a callee's replacement.
 *)
Theory rawFmpTransportDefs
Ancestors
  instIdxIndep

Definition raw_fmp_result_rel_def:
  raw_fmp_result_rel p i e r r' =
    case r of
      Error msg => r' = Error msg
    | OK s =>
        r' = OK (s with <|vs_fmp := p; vs_initial_fmp := i;
                          vs_call_entry_fmp := e|>)
    | IntRet ret s =>
        r' = IntRet ret (s with <|vs_fmp := p; vs_initial_fmp := i;
                                  vs_call_entry_fmp := e|>)
    | Halt s =>
        ?e'. r' = Halt (s with <|vs_fmp := p; vs_initial_fmp := i;
                                 vs_call_entry_fmp := e'|>)
    | Abort a s =>
        ?e'. r' = Abort a (s with <|vs_fmp := p; vs_initial_fmp := i;
                                    vs_call_entry_fmp := e'|>)
End

Theorem raw_fmp_result_rel_cases[simp]:
  (raw_fmp_result_rel p i e (Error msg) r' <=> r' = Error msg) /\
  (raw_fmp_result_rel p i e (OK s) r' <=>
     r' = OK (s with <|vs_fmp := p; vs_initial_fmp := i;
                       vs_call_entry_fmp := e|>)) /\
  (raw_fmp_result_rel p i e (IntRet ret s) r' <=>
     r' = IntRet ret (s with <|vs_fmp := p; vs_initial_fmp := i;
                               vs_call_entry_fmp := e|>)) /\
  (raw_fmp_result_rel p i e (Halt s) r' <=>
     ?e'. r' = Halt (s with <|vs_fmp := p; vs_initial_fmp := i;
                              vs_call_entry_fmp := e'|>)) /\
  (raw_fmp_result_rel p i e (Abort a s) r' <=>
     ?e'. r' = Abort a (s with <|vs_fmp := p; vs_initial_fmp := i;
                                 vs_call_entry_fmp := e'|>))
Proof
  simp[raw_fmp_result_rel_def]
QED

Theorem raw_fmp_result_rel_uniform:
  raw_fmp_result_rel p i e r
    (exec_result_map
      (\s. s with <|vs_fmp := p; vs_initial_fmp := i;
                    vs_call_entry_fmp := e|>) r)
Proof
  Cases_on `r` >> simp[exec_result_map_def] >>
  qexists_tac `e` >> simp[]
QED
