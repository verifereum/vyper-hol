(* Complete memory endpoints and composite augmented-place consumers. *)
Theory augAssignPlaceCompositeMemory
Ancestors
  augAssignPlaceCompileMemory augAssignPlaceLoadContinuation
  augAssignPlaceSourceMemory augAssignPlaceRhsContinuation
  augAssignPlaceMemoryContinuation bodyMemoryDefs exprSimMemDefs
  bodyAugAssignOther targetPlaceSimMem

Theorem aug_place_memory_post[local]:
  res = INL () /\
  stmt_post ctx func cx lctx cenv cenv sa sb s0 res ee t /\
  return_buf_frame d cenv sa s0 /\
  sa.cs_next_var <= sb.cs_next_var /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?cenv'. stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
    cenv_top_ext cenv cenv' ee.scopes /\
    stmt_state_rel ctx func cenv' cx ee t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    return_buf_frame d cenv' sb t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> qexists_tac `cenv` >>
  gvs[stmtSimDefsTheory.stmt_post_def] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]
QED
