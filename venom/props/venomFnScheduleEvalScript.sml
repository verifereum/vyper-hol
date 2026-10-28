(* Symbolic composition laws for bounded evaluation of function schedules.
   The unit, function and supply payloads stay schematic in these proofs. *)
Theory venomFnScheduleEval
Ancestors venomFnScheduleRunner list

Theorem run_configured_fn_pass_fold_append:
  !prefix runner rpolicy suffix cu supply func labels.
    run_configured_fn_pass_fold runner rpolicy (prefix ++ suffix) cu supply func labels =
    case run_configured_fn_pass_fold runner rpolicy prefix cu supply func labels of
      NONE => NONE
    | SOME (next_func,next_labels,next_supply) =>
        run_configured_fn_pass_fold runner rpolicy suffix cu
          next_supply next_func next_labels
Proof
  Induct >> simp[run_configured_fn_pass_fold_def] >> rpt gen_tac >>
  BasicProvers.every_case_tac >> simp[]
QED

Theorem run_configured_fn_pass_fold_two:
  run_configured_fn_pass_fold runner rpolicy (first::second::rest) cu supply func labels =
  case run_configured_fn_pass_fold runner rpolicy [first] cu supply func labels of
    NONE => NONE
  | SOME (next_func,next_labels,next_supply) =>
      run_configured_fn_pass_fold runner rpolicy (second::rest) cu
        next_supply next_func next_labels
Proof
  mp_tac (Q.SPECL [`[first]`,`runner`,`rpolicy`,`second::rest`,
    `cu`,`supply`,`func`,`labels`] run_configured_fn_pass_fold_append) >> simp[]
QED
