Theory abiMalformedEntryProps
Ancestors
  abiMalformedRecursiveInterface
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem abi_malformed_entry_allocas_below_fmp:
  abi_malformed_entry H ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d n s ==>
  ctx_has_dalloca ctx ==> allocas_below_fmp s
Proof
  rewrite_tac[abi_malformed_entry_def] >> strip_tac >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  disch_then ACCEPT_TAC
QED
