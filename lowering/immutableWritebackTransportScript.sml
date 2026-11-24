Theory immutableWritebackTransport
Ancestors
  compileEnv loweringStateRelDefs

Theorem immutable_writeback_at_active_horizon:
  A /\ B /\
  (!h ts. ALOOKUP cenv.ce_modules cenv.ce_module = SOME ts /\
    stmt_state_rel h ctx func cenv cx ee s ==> stmt_state_rel h ctx func cenv cx ef q) /\ Tail ==>
  !h0 active. ALOOKUP cenv.ce_modules cenv.ce_module = SOME active /\
    stmt_state_rel h0 ctx func cenv cx ee s ==>
  A /\ B /\ stmt_state_rel h0 ctx func cenv cx ef q /\ Tail
Proof
  metis_tac[]
QED
