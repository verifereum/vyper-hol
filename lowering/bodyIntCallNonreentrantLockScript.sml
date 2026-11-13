(* The nonreentrant guard of an internal callee, against the source.

   The source takes the lock in the caller, with lock_if_nr just before
   push_function (intcall_entry), and releases it with unlock_if_nr after
   pop_function (intcall_rest).  The compiled callee takes it in its
   prologue, after the entry prefix, and releases it in its epilogue, just
   before RET (compile_internal_function_entry_factorization).  These two
   fragments relate the compiled lock and unlock to those source actions
   under state_rel.

   Both assume that the context's slot is the one the compiler uses.  The
   external-entry analogues (nonreentrantEntryEquivTheory) derive it from
   layouts_agree; whether body_inv carries it or the leaves take it as a
   premise is still open, so it is a premise here. *)
Theory bodyIntCallNonreentrantLock
Ancestors
  bodyIntCallSeamDefs exprSimDefs fragExec nonreentrantEquiv

(* The callee prologue's lock: TLOAD, EQ 1, ISZERO, ASSERT, and TSTORE 1
   unless view.  It passes exactly when the source's lock_if_nr does, and
   then leaves the two related again; when the lock is held, both fail. *)
Theorem intcall_nonreentrant_lock_frag:
  !ctx func ce cx es s sa sb view.
    cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
    nonreentrant_slot_separated cx /\
    compile_nonreentrant_lock global_nonreentrant_slot T view sa = ((),sb) /\
    state_rel func ce cx es s /\ fresh_vars_wrt sa s ==>
    frag_exec ctx sa sb (\x. x = s)
      (\x. ?es'. lock_if_nr cx T view es = (INL (),es') /\
                 state_rel func ce cx es' x /\ fresh_vars_wrt sb x /\
                 x.vs_memory = s.vs_memory /\ x.vs_allocas = s.vs_allocas /\
                 x.vs_alloca_next = s.vs_alloca_next /\
                 !op w. eval_operand op s = SOME w ==> eval_operand op x = SOME w)
      (\r. ?err. lock_if_nr cx T view es = (INR err,es) /\
                 expr_exit (INR err) r)
Proof
  cheat
QED

(* The callee epilogue's unlock: TSTORE 0 unless view, just before RET.
   It matches the source's unlock_if_nr and keeps the two related. *)
Theorem intcall_nonreentrant_unlock_frag:
  !ctx func ce cx es s sa sb view.
    cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
    compile_nonreentrant_unlock global_nonreentrant_slot T view sa = ((),sb) /\
    state_rel func ce cx es s ==>
    frag_exec ctx sa sb (\x. x = s)
      (\x. ?es'. unlock_if_nr cx T view es = (INL (),es') /\
                 state_rel func ce cx es' x /\
                 x.vs_memory = s.vs_memory /\ x.vs_allocas = s.vs_allocas /\
                 x.vs_alloca_next = s.vs_alloca_next /\
                 !op w. eval_operand op s = SOME w ==> eval_operand op x = SOME w)
      (\r. F)
Proof
  cheat
QED
