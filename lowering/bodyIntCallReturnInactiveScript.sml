(* An internal return whose frame holds no reentrancy guard: the return
   epilogue emits no unlock and leaves the state unchanged. *)
Theory bodyIntCallReturnInactive
Ancestors
  stmtSimReturn stmtLowering compileEnv

Theorem return_unlock_state_inactive:
  !cenv. ~FST cenv.ce_nonreentrant ==> !s. return_unlock_state cenv s = s
Proof
  rpt strip_tac >> Cases_on `cenv.ce_nonreentrant` >> PairCases_on `r` >>
  fs[return_unlock_state_def]
QED

Theorem compile_return_unlock_inactive:
  !cenv. ~FST cenv.ce_nonreentrant ==> compile_return_unlock cenv = comp_return ()
Proof
  rpt strip_tac >> Cases_on `cenv.ce_nonreentrant` >> PairCases_on `r` >>
  fs[compile_return_unlock_def]
QED
