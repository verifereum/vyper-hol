Theory algebraicOptCorrectness
Ancestors
  algebraicOptProofs venomWf

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
    (* No INVOKE in function (standard for state_equiv-based proofs) *)
    (!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> INVOKE) /\
    (* Freshness: original operands/outputs don't use fresh variable names *)
    (!inst v. MEM inst (fn_insts fn) /\
              MEM (Var v) inst.inst_operands ==> v NOTIN fv) /\
    (!inst v. MEM inst (fn_insts fn) /\
              MEM v inst.inst_outputs ==> v NOTIN fv) /\
    (* Well-formedness *)
    ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    (* DFG invariant: ADDRESS/SIGNEXTEND outputs consistent with initial state.
       Trivially true when these output vars are undefined in s (the typical case). *)
    (!x inst. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs /\
      (inst.inst_opcode = ADDRESS \/ inst.inst_opcode = SIGNEXTEND) ==>
      lookup_var x s = NONE)
    ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv fv') (execution_equiv fv') (execution_equiv fv')
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (ao_transform_function fn) s)
Proof
  ACCEPT_TAC ao_transform_function_correct_proof
QED

(* ===== Structural Preservation ===== *)

(* ao_fresh_id produces IDs > fn_max_inst_id, so they are distinct from
   all original IDs and from each other (injective).  The other wf_function
   components (labels, entry, bb_well_formed, succs_closed) are preserved
   by the MAP-based block transform structure. *)
Theorem ao_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (ao_transform_function fn)
Proof
  cheat
QED

(* Fresh output variables (ao_fresh_var) are distinct from original outputs
   and written exactly once.  Requires ao_fresh_var injectivity and
   non-collision with existing variable names. *)
Theorem ao_preserves_ssa_form:
  !fn. ssa_form fn /\ wf_function fn ==> ssa_form (ao_transform_function fn)
Proof
  cheat
QED

(* ===== Remaining Semantic Obligations =====

   The correctness proof depends on three cheated theorems, each in
   its own file for independent parallel development:

   1. aoResolveObligationScript.sml — ao_resolve_iszero_inst_sim
      Iszero chain resolution is a semantic no-op.
      NOTE: current formulation (∀s) needs reformulation with a
      state-dependent chain invariant.

   2. aoRangeObligationScript.sml — range_analyze_sound
      Range analysis produces correct bounds.

   3. aoCmpFlipObligationScript.sml — ao_cmp_flip_block_sim
      Cmp_flip preserves block execution up to dead variables.

   ===== *)
