(*
 * Common Subexpression Elimination — Proofs
 *
 * Correctness: CSE with canon map + operand identity is sound.
 *
 * The available expression analysis with root-only effect removal is an
 * overapproximation (keeps expressions with invalidated sub-expressions).
 * The canon map + operand_ids_match check ensures that CSE only replaces
 * instructions whose operands provably evaluate to the same values as
 * the source instruction's operands (via SSA + ASSIGN chain equivalence).
 *
 * Proof sketch (out of scope, all cheated):
 *   1. operand_ids_match → same canonical producers → same var values (SSA)
 *   2. same var values → same operand evaluation (eval_operand determinism)
 *   3. same opcode + same operand values → same step_inst output
 *   4. source was executed → output var holds result (SSA: written once)
 *   5. therefore ASSIGN from source output is correct
 *)

Theory cseProofs
Ancestors
  cseDefs analysisSimProps passSimulationProps

(* CSE soundness: for every ae entry where operand_ids_match holds,
   the source variable holds the same value that re-executing the
   instruction would produce. This is weaker than full ae soundness —
   it only applies when the canon map confirms operand identity. *)
Definition cse_sound_def:
  cse_sound (canon : canon_map) (dfg : dfg_analysis)
            (av_opt : avail_exprs option) (s : venom_state) <=>
    case av_opt of
      NONE => T
    | SOME av =>
        !expr srcs src_inst src_var.
          FLOOKUP av expr = SOME srcs /\
          MEM src_inst srcs /\
          src_inst.inst_outputs = [src_var] ==>
          (* Source variable is defined *)
          (?w. FLOOKUP s.vs_vars src_var = SOME w) /\
          (* For instructions with matching operand identity,
             source's output matches what inst would compute *)
          (!inst fuel ctx s'.
             mk_expr dfg inst = expr /\
             operand_ids_match canon dfg inst src_inst /\
             inst.inst_outputs <> [] /\
             step_inst fuel ctx inst s = OK s' ==>
             FLOOKUP s.vs_vars src_var =
             FLOOKUP s'.vs_vars (HD inst.inst_outputs))
End

Theorem cse_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (cse_function fn) s)
Proof
  cheat
QED
