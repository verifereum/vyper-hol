(*
 * A runtime call of a checked single-module contract writes no immutables.
 *)
Theory vyperRuntimeImmutables
Ancestors
  vyperInterpreter vyperState vyperTypeContract vyperCall

(* Intuition: st.immutables changes only through set_immutable, reached from
   write_place / pop_place on an ImmutablePlace, which lookup_global yields
   only for a name with no storage, transient or hashmap declaration.
   check_contract F checks every non-Deploy body and default argument of the
   (fully live) main module with no assignable bare globals, so every write
   target type-checks to a storage, transient or hashmap declaration. The
   entry is a checked External function or a getter; internal calls reach
   only Internal functions (lookup_callable_function F); eval_create keeps
   immutables (eval_create_preserves_scopes_immutables); external calls are
   oracle outcomes; constants are not evaluated outside deployment; error
   paths return am, and finalize_pending_deletions keeps immutables. *)
Theorem call_external_runtime_preserves_immutables:
  check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  call_external orc gobs am tx = (res, am', rqs) ==>
  am'.immutables = am.immutables
Proof
  cheat
QED
