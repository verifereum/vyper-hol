(* Constructor-supported cleanup for exempt errors; halt skips cleanup. *)
Theory bodyIntCallNRExemptCleanup
Ancestors
  gasExemptCert vyperState vyperInterpreter
Libs
  monadsyntax

Theorem total_finally_unless_halt_try:
  (!st. ?u. g st = (INL (),u)) ==>
  finally_unless_halt f g =
  try (bind f (\v. ignore_bind g (return v)))
    (\ex. if ex = HaltException then raise ex else ignore_bind g (raise ex))
Proof
  strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  Cases_on `f x` >> rename1 `f x = (res,st)` >>
  first_x_assum (qspec_then `st` strip_assume_tac) >>
  Cases_on `res`
  >- simp[finally_unless_halt_def, try_def, bind_def, ignore_bind_def, return_def] >>
  rename1 `f x = (INR ex,st)` >> Cases_on `ex` >>
  simp[finally_unless_halt_def, try_def, bind_def, ignore_bind_def,
       return_def, raise_def]
QED
