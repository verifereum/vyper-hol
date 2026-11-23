Theory bodyFullAbiDecodeOwnedStateProps
Ancestors
  exprLoweringProps ptrDiscipline
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem owned_decoder_allocas_below_fmp:
  (?H. V H) /\ (!H. V H ==> stmt_state_rel H ctx fn ce cx es s) ==>
  ctx_has_dalloca ctx ==> allocas_below_fmp s
Proof
  metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp]
QED
