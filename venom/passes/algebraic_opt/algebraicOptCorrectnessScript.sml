Theory algebraicOptCorrectness
Ancestors
  algebraicOptProofs algebraicOptWf venomWf

(* Algebraic optimization preserves function execution semantics:
   running a function before and after the transform produces
   equivalent results under state_equiv and execution_equiv,
   modulo fresh variables and cmp_flip dead variables.
   ao_fn_total_fresh_vars includes both ao_fn_fresh_vars (peephole expansion
   intermediates) and ao_cmp_flip_dead_vars (comparator outputs whose values
   change under the flip but are dead after their block). *)
(* Correctness: for non-erroneous executions, the transform preserves semantics.
   The Error disjunct: if the original function errors (undefined variable,
   out-of-fuel, etc.), we make no guarantee about the transformed version.
   For well-formed SSA programs, the Error case does not arise. *)
Theorem ao_transform_function_correct:
  !fuel ctx fn s.
    let fv = ao_fn_fresh_vars fn in
    let fv' = ao_fn_total_fresh_vars fn in
    (* Freshness: original operands/outputs don't use fresh variable names *)
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    (* Well-formedness *)
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    (* DFG invariant: ADDRESS/SIGNEXTEND outputs consistent with initial state.
       Trivially true when these output vars are undefined in s (the typical case). *)
    (!x inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
      (inst.inst_opcode = ADDRESS \/ inst.inst_opcode = SIGNEXTEND) ==>
      lookup_var x s = NONE) /\
    fn_entry_label fn = SOME s.vs_current_bb
    ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fv') (execution_equiv fv') (execution_equiv fv')
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  ACCEPT_TAC ao_transform_function_correct_proof
QED

(* ===== Structural Preservation ===== *)

Theorem ao_preserves_wf_function =
  algebraicOptWfTheory.ao_preserves_wf_function

Theorem ao_preserves_ssa_form =
  algebraicOptWfTheory.ao_preserves_ssa_form

(* ===== Remaining Semantic Obligations =====

   The correctness proof depends on cheated theorems in separate files
   for independent parallel development:

   DONE (0 cheats):
   1. aoResolveObligationScript.sml — ao_resolve_iszero_inst_sim
      Iszero chain resolution is a semantic no-op.
   2. aoRangeObligationScript.sml — range_analyze_sound
      Range analysis produces correct bounds.

   DONE (0 cheats):
   4. aoStepInvObligationScript.sml — step-level invariant obligations:
      in_range_state/sinv compat with state_equiv, sinv step preservation,
      chain variable freshness.

   IN PROGRESS:
   3. aoCmpFlipObligationScript.sml — ao_cmp_flip_block_sim
      Cmp_flip preserves block execution up to dead variables.
   5. aoBlockInvObligationScript.sml — block-level invariant obligations:
      chain_inv/chains_defined through exec_block, range_sound + cfg at
      successor, initial state establishment.
   6. algebraicOptProofsScript.sml — chain_inv transfer_sound:
      ao_iszero_chain_inv step-preservation via SSA output freshness.
      Requires adding freshness tracking to the sound condition.

   ===== *)
