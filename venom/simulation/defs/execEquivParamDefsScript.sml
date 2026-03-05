(*
 * Parameterized Execution Equivalence — Definitions
 *
 * Closure conditions on a state relation R that enable
 * step_inst_preserves_R (the master theorem).
 *
 * Both state_equiv and state_equiv_except satisfy valid_state_rel.
 * This eliminates per-pass boilerplate (~800 LOC each for RTA, phi-elim, etc.)
 *
 * TOP-LEVEL:
 *   valid_state_rel — closure conditions on R for execution preservation
 *)

Theory execEquivParamDefs
Ancestors
  stateEquiv venomSem venomState venomInst

(* Closure conditions on a state relation R.
   Any R satisfying these supports step_inst_preserves_R.

   Conservative: requires all non-var fields equal.
   Can be weakened later if a pass only needs partial field equality. *)
Definition valid_state_rel_def:
  valid_state_rel (R : venom_state -> venom_state -> bool) <=>
    (* R preserves execution-relevant state fields *)
    (!s1 s2. R s1 s2 ==>
      s1.vs_call_ctx = s2.vs_call_ctx /\
      s1.vs_tx_ctx = s2.vs_tx_ctx /\
      s1.vs_block_ctx = s2.vs_block_ctx /\
      s1.vs_accounts = s2.vs_accounts /\
      s1.vs_memory = s2.vs_memory /\
      s1.vs_storage = s2.vs_storage /\
      s1.vs_transient = s2.vs_transient /\
      s1.vs_returndata = s2.vs_returndata /\
      s1.vs_halted = s2.vs_halted /\
      s1.vs_prev_bb = s2.vs_prev_bb /\
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx) /\
    (* R closed under var update *)
    (!s1 s2 x v. R s1 s2 ==> R (update_var x v s1) (update_var x v s2)) /\
    (* R preserves eval_operand when operand var agrees *)
    (!s1 s2 op. R s1 s2 /\
       (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
       eval_operand op s1 = eval_operand op s2) /\
    (* R reflexive *)
    (!s. R s s)
End
