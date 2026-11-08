(* Shared introduction for the normal branch of stmt_frag_ptr. *)
Theory augAssignPtrStorePost
Ancestors
  bodyPtrDefs augAssignPtrStore augAssignPtrStorageStore augAssignPtrFieldStorePost

Theorem stmt_frag_ptr_normal_post:
  stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
  ~block_is_terminated sb /\ cenv_top_ext cenv cenv' ee.scopes /\
  stmt_state_rel ctx func cenv' cx ee t /\
  ghost_inv d cenv' cx ee G tn t /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x t = SOME w) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP G x = FLOOKUP G0 x /\
       op_taint tn (Var x) = op_taint tn0 (Var x)) ==>
  ?cenv''.
    stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
    (INL () = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
    cenv_top_ext cenv cenv'' ee.scopes /\
    stmt_state_rel ctx func cenv'' cx ee t /\
    ghost_inv d cenv'' cx ee G tn t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >> qexists_tac `cenv'` >> simp[]
QED
