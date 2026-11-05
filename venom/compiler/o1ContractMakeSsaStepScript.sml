(*
 * MakeSSA's step contract, for both of its O1 runs: the output keeps the
 * O1 function shape, its fresh names and instruction ids come from the
 * supply, it maps no labels, the supply stays ok, and it adds no ALLOCA
 * (the only function row).
 *)
Theory o1ContractMakeSsaStep
Ancestors
  o1PassContract makeSsaCurrentDefs venomPassSchedule irSupply

(* Notes on why this holds (the prover may ignore them).
 *
 * The input only has o1_fn_shape: it need not be SSA, and a variable may be
 * read on a path where nothing defines it.  make_ssa_current_fn is the
 * identity when fn_entry_label is NONE.  Otherwise it keeps every block
 * label, block order and terminator label; it inserts PHIs (fresh ids) at
 * the head of dominance-frontier blocks; it renames along the dominator tree
 * only (unreachable blocks keep their instructions as they are); the first
 * renamed definition of a variable keeps its spelling and later ones get
 * fresh_ir_var names; operands are renamed to the latest version of the same
 * variable; simplify_current_phis (only when the input already had leading
 * PHIs) turns a PHI into ASSIGN/NOP or keeps it.
 *
 * - compute_df only adds join points (more than one predecessor), so the
 *   first block (no predecessors) gets no PHI, and every inserted PHI has at
 *   least two pairs, one per CFG predecessor.
 * - Every output variable v' is a version of exactly one input variable v
 *   (v' = v, or v' a fresh name made for v), and each output instruction is
 *   either the renamed image of an input one (same opcode, or ASSIGN/NOP
 *   from a PHI; outputs and Var operands mapped to versions) or an inserted
 *   PHI (or its ASSIGN/NOP collapse) whose output and Var operands are all
 *   versions of one variable.  So copy_phi_var origin fn' v' implies
 *   copy_phi_var origin fn v: this gives the DALLOCA clause (a DALLOCA's
 *   output is its own input output's version) and opaque_use_ok, and with
 *   fresh names distinct, the single-writer clauses of retpc_shape_ok.
 * - retpc_shape_ok's reachable clauses go the other way: every version of a
 *   return-PC variable that the output reaches is a return-PC variable of
 *   the output.  A return-PC variable has one writer (clause 4 of the
 *   input), in a block B; its other versions are PHIs at iterated frontiers
 *   of B, each with an operand from a predecessor dominated by a block
 *   holding an earlier version, whose rename stack therefore holds a version
 *   connected to B's definition (not the bare initial spelling).
 *)
Theorem make_ssa_step_contract_at:
  k = 0 \/ k = 4 ==> o1_step_contract_at k rpolicy (CFP_Simple VP_MakeSSA)
Proof
  cheat
QED
