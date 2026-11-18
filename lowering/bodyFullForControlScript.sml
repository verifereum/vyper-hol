(* Halt observations survive the loop body's source scope cleanup. *)
Theory bodyFullForControl
Ancestors
  exprSimDefs loweringStateRelDefs vyperState

Theorem halt_exit_scopes_gas_obs:
  halt_exit H cx ee res r ==>
  halt_exit H cx (ee with <| scopes := sc; gas_obs := g |>) res r
Proof
  simp[halt_exit_def, loweringStateRelDefsTheory.halt_rel_def,
       loweringStateRelDefsTheory.accounts_rel_def]
QED
