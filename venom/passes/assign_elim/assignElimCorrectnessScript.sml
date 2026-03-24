(*
 * Assign Elimination — Correctness Statement
 *
 * Copy propagation preserves semantics: replacing Var x with Var y
 * where x := assign y gives the same value because copy_sound ensures
 * lookup_var x s = lookup_var y s at every use site.
 *
 * Variables that are outputs of NOP'd ASSIGNs are excluded from
 * equivalence (assign_elim_eliminated_vars). These variables are dead
 * after copy propagation substitutes all their uses with the source.
 *
 * The error disjunct covers the edge case where a forwardable ASSIGN's
 * Var source is undefined at runtime. In SSA programs with proper
 * dominance, this is unreachable, but we don't have a formal dominance
 * predicate so it appears as a disjunct.
 *
 * Preconditions:
 *   wf_function fn — well-formed function (unique labels, entry, bb_well_formed)
 *   fn_inst_wf fn — all instructions structurally well-formed
 *   s.vs_inst_idx = 0 — standard execution entry point
 *   fn_entry_label fn = SOME s.vs_current_bb — execution starts at entry
 *   non-terminator interior — no non-last instruction is a terminator
 *   operand_cond — no instruction in the substituted function reads
 *     an eliminated variable (holds in SSA form)
 *)

Theory assignElimCorrectness
Ancestors
  assignElimProofs

Theorem assign_elim_function_correct:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    wf_function fn /\
    fn_inst_wf fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb inst x.
       MEM bb fn_subst.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN elim) ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assign_elim_function fn) s)
Proof
  ACCEPT_TAC assign_elim_function_correct_proof
QED
