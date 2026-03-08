(*
 * Parameterized Execution Equivalence — Definitions
 *
 * Closure conditions on a (R_ok, R_term) relation pair that enable
 * step_inst_preserves_R (the master theorem).
 *
 * (state_equiv vars, execution_equiv vars) satisfies valid_state_rel.
 * This eliminates per-pass boilerplate (~800 LOC each for RTA, phi-elim, etc.)
 *
 * TOP-LEVEL:
 *   valid_state_rel — closure conditions on (R_ok, R_term) pair
 *)

Theory execEquivParamDefs
Ancestors
  stateEquiv venomExecSemantics venomState venomInst

(* Closure conditions on a (R_ok, R_term) relation pair.
   Any pair satisfying these supports step_inst_preserves_R.

   R_ok: used for OK results (continuation). Must preserve all state fields
         including control flow (needed for block_sim_function fuel induction).
   R_term: used for Halt/Revert results (terminal). May omit control flow
           fields since execution has stopped.

   Both must be closed under update_var and preserve eval_operand. *)
Definition valid_state_rel_def:
  valid_state_rel
    (R_ok : venom_state -> venom_state -> bool)
    (R_term : venom_state -> venom_state -> bool) <=>
    (* R_ok preserves all execution-relevant state fields including control flow *)
    (!s1 s2. R_ok s1 s2 ==>
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
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_params = s2.vs_params) /\
    (* R_term preserves execution-relevant fields (may omit control flow) *)
    (!s1 s2. R_term s1 s2 ==>
      s1.vs_call_ctx = s2.vs_call_ctx /\
      s1.vs_tx_ctx = s2.vs_tx_ctx /\
      s1.vs_block_ctx = s2.vs_block_ctx /\
      s1.vs_accounts = s2.vs_accounts /\
      s1.vs_memory = s2.vs_memory /\
      s1.vs_storage = s2.vs_storage /\
      s1.vs_transient = s2.vs_transient /\
      s1.vs_returndata = s2.vs_returndata /\
      s1.vs_halted = s2.vs_halted /\
      s1.vs_params = s2.vs_params) /\
    (* Both closed under var update *)
    (!s1 s2 x v. R_ok s1 s2 ==>
                  R_ok (update_var x v s1) (update_var x v s2)) /\
    (!s1 s2 x v. R_term s1 s2 ==>
                  R_term (update_var x v s1) (update_var x v s2)) /\
    (* Both preserve eval_operand when operand var agrees *)
    (!s1 s2 op. R_ok s1 s2 /\
       (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
       eval_operand op s1 = eval_operand op s2) /\
    (!s1 s2 op. R_term s1 s2 /\
       (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
       eval_operand op s1 = eval_operand op s2) /\
    (* Both reflexive *)
    (!s. R_ok s s) /\
    (!s. R_term s s)
End
