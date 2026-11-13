(* Successful binding checks, rather than changes, original source values. *)
Theory entryArgumentCastFacts
Ancestors loweringHalt vyperTyping vyperInterpreter list pair

(* safe_cast_some_eq already exports the mutual cast/list identity theorem. *)
Theorem safe_cast_original_value_typed:
  safe_cast tv v = SOME out ==> value_has_type tv v
Proof
  metis_tac[safe_cast_some_eq, safe_cast_result_well_typed]
QED

Theorem bind_arguments_source_values:
  bind_arguments tenv args vals = SOME env ==>
  LIST_REL (\(name,ty) v. ?tv.
    evaluate_type tenv ty = SOME tv /\ safe_cast tv v = SOME v /\
    value_has_type tv v) args vals
Proof
  map_every qid_spec_tac [`env`,`vals`] >> Induct_on `args`
  >- (Cases_on `vals` >> simp[bind_arguments_def]) >>
  gen_tac >> PairCases_on `h` >> Cases_on `vals` >> simp[Once bind_arguments_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  drule safe_cast_original_value_typed >> strip_tac >>
  drule (cj 1 safe_cast_some_eq) >> strip_tac >> gvs[] >>
  metis_tac[]
QED
