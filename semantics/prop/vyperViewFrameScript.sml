(*
 * Checked view and pure external calls do not change the machine.
 *
 * check_contract accepts a function body only if it respects its declared
 * mutability (function_mutability_ok, following Vyper's local.py): a view or
 * pure function writes no storage, transient storage or immutable, emits no
 * log, sends no value, creates or destroys no contract, calls internal
 * functions only of mutability view or pure, and makes only static external
 * calls.  So a successful call of a checked view or pure entry returns the
 * machine it started from.  A nonreentrant view function only reads its lock
 * (acquire_nonreentrant_lock's is_view form) and never releases it.
 *
 * TOP-LEVEL: call_external_view_frame.
 *)

Theory vyperViewFrame
Ancestors
  vyperInterpreter vyperTypeContract vyperTypeSelectedEntry vyperReadOnlyExternal

val _ = Parse.hide "body";

(* TOP-LEVEL: a successful call of a checked @view or @pure external entry
   (an external function or a public getter) leaves accounts, storage,
   transient storage, immutables, logs and pending deletions as they were;
   call_external's finalize_pending_deletions step is the only difference,
   and it is the identity when no deletion is pending. *)
(* Why it holds (notes for the proof, not part of the statement):
   - check_contract checks every FunctionDecl of every module
     (check_module / check_toplevel_decl), so every internal callee a view
     body reaches is declared View or Pure and its body passed
     stmts_mutability_ok at that mutability; Pure-ok implies View-ok.  At
     runtime IntCall finds the callee as call_target_mutability_ok does
     (get_module_code then lookup_callable_function with in_deploy = F).
   - The frame (accounts, tStorage, logs, immutables, pending_deletions)
     must hold for every result of eval_stmt/eval_expr, not only INL:
     IntCall's finally, For's handle_loop_exception and raw_call with
     revert_on_failure = F continue after failures.
   - Static calls: in oracle mode ExtCall with is_static has value NONE, so
     the request is static and adopt_call_outcome leaves the state alone;
     raw_call always runs run_raw_call.  Without an oracle, a static call
     runs verifereum's run_call in a static context:
     vfmStaticCallsTheory.run_static_preserves covers run (run_call is a
     restriction of run), and precompiles touch only the call context.
     Failed calls return the original accounts and tStorage.
   - Getters (external_getter_tuple) are View, not nonreentrant, with body
     [Return (SOME e)] for a Subscript chain over a TopLevelName, which is
     itself stmts_mutability_ok at View.
   - The view lock is acquire_nonreentrant_lock's is_view form (a read);
     send_call_value fails unless the value is 0; evaluate_defaults works
     on a throwaway state; with in_deploy = F, am_c = am. *)
Theorem call_external_view_frame:
  check_contract F am.layouts tx.target mods = SOME art /\
  selected_entry am tx mods (mut,nr,args,dflts,ret,body) /\
  (mut = View \/ mut = Pure) /\
  call_external orc gobs am tx = (INL v, am', rqs) ==>
  am' = finalize_pending_deletions am
Proof
  strip_tac >>
  drule selected_entry_module_code >>
  disch_then (qspec_then `find_function_module am tx.target tx.function_name`
                mp_tac) >>
  simp[] >> strip_tac >>
  `call_external orc gobs am tx =
     case call_external_function orc gobs am
            (initial_evaluation_context am.sources am.layouts tx
               (find_function_module am tx.target tx.function_name))
            nr mut ts mods args dflts tx.args body ret of
       (INL value, am1, rqs1) => (INL value, finalize_pending_deletions am1, rqs1)
     | failure => failure` by (irule call_external_selected_entry >> fs[]) >>
  gvs[AllCaseEqs()] >>
  drule_at (Pos last) selected_entry_external_function_frame >> simp[] >>
  disch_then drule_all >> simp[]
QED
