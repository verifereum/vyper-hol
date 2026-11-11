(*
 * Assert Combiner — semantic correctness.
 *
 * The structural obligations (SSA form, wf_function, fn_inst_wf, and the
 * supply staying valid and covering the result) are in acSupplyProofs.
 *
 * Why it holds (intuition, not a prescribed proof):
 *
 *  - Inside a block the transform turns   ASSERT a; ...; ASSERT b
 *    (a = ISZERO p1, b = ISZERO p2, possibly through ASSIGN chains, and
 *    only ac_is_safe_between instructions in between) into
 *    NOP; ...; t = OR p1 p2; u = ISZERO t; ASSERT u.  t and u are fresh
 *    (outside the supply that covers fn), so on every path the original
 *    passes, the transformed run differs only in fresh variables.
 *  - When the original aborts at the first assert, the transformed run
 *    executes the instructions in between and aborts at the merged assert.
 *    Those instructions have no effects, so the abort states differ only
 *    in variables (execution_equiv UNIV) and in the GAS readings consumed
 *    by a GAS instruction in between (ac_abort_equiv).  The in-between
 *    instructions can't fail on an operand in the transformed run: a Var
 *    operand is defined (SSA dominance, below, or an earlier in-between
 *    instruction) and a Label operand is in vs_labels (the premise).
 *  - The source predicates p1 and p2 hold the value the DFG says when the
 *    ASSERTs run.  Not because variables are never redefined (they are, on
 *    a loop back edge), but by dominance: in wf_ssa every use is dominated
 *    by its unique definition, so when control is at instruction idx of
 *    bb, every definition strictly dominating that point has run, and its
 *    output and the operands it read still hold their values (nothing
 *    after it on the path redefines them).  This is the invariant to
 *    carry: the DFG ISZERO/ASSIGN facts (acChainProofs's ac_dfg_inv_local)
 *    for the definitions that strictly dominate the cursor (bb, idx),
 *    together with strict_dom_vars_defined (venomWfProps) and
 *    reachability, all about the original run.  ssa_unique_output_block
 *    and fn_dominates_antisym (venomWfProps) show the instruction at the
 *    cursor can't overwrite what that invariant talks about.  PHIs (at
 *    block entry, eval_phis) are never merged and keep it.
 *  - Blocks keep their labels and successor structure, so the simulation
 *    is block by block, starting at inst index 0 of each block (the
 *    transform inserts instructions, so mid-block indices don't
 *    correspond).  INVOKE runs the same callee on both sides.
 *  - An Error of the original run is excused (first disjunct).
 *)

Theory assertCombinerCorrectness
Ancestors
  acSupplyProofs acChainProofs acAbortRelProofs acBaseProofs
  assertCombinerDefs irSupply irSupplyFreshProps venomFnScheduleRunner
  stateEquiv stateEquivProps venomWf venomWfProps venomExecSemantics
  venomExecProofs venomInstIdsProps venomInst list

(* The assert combiner preserves semantics: on every run where the original
   doesn't error, the transformed function ends the same way.  OK and halt
   states agree up to the variables the transform took from the supply;
   revert states fully; abort states up to the remaining GAS readings,
   since a GAS read between the two merged asserts still runs in the
   transformed function after the original has aborted at the first. *)
Theorem ac_transform_function_correct:
  !fuel ctx fn su s.
    wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
    ir_supply_covers_fn su fn /\
    (!inst l. MEM inst (fn_insts fn) /\ ac_is_safe_between inst /\
              MEM (Label l) inst.inst_operands ==> l IN FDOM s.vs_labels) /\
    s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv (ac_fresh_vars su fn)) (execution_equiv UNIV)
      (\s1 s2. ?gs. execution_equiv UNIV s1 (s2 with vs_gas_readings := gs))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (FST (ac_transform_function su fn)) s)
Proof
  cheat
QED
