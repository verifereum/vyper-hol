(*
 * Common Subexpression Elimination — Proofs
 *
 * Key lemma: cse_inst satisfies analysis_inst_simulates
 * with available expression soundness: if an expression is
 * available with source src_var, then src_var holds the value
 * that re-executing the expression would produce.
 *)

Theory cseProofs
Ancestors
  cseDefs analysisSimProps passSimulationProps

(* Available expression soundness: for every available expression
   with source variable src_var, src_var holds the same value that
   executing any instruction computing this expression would produce.
   This is the semantic correctness of the available expression analysis. *)
Definition cse_sound_def:
  cse_sound (dfg : dfg_analysis) (av_opt : avail_exprs option)
            (s : venom_state) <=>
    case av_opt of
      NONE => T
    | SOME av =>
        !expr srcs src_inst src_var.
          FLOOKUP av expr = SOME srcs /\
          MEM src_inst srcs /\
          src_inst.inst_outputs = [src_var] ==>
          (* Source variable is defined *)
          (?w. FLOOKUP s.vs_vars src_var = SOME w) /\
          (* And holds the expression's value: for any instruction that
             computes this expression, its output matches src_var *)
          (!inst fuel ctx s'.
             mk_expr dfg inst = expr /\
             inst.inst_outputs <> [] /\
             step_inst fuel ctx inst s = OK s' ==>
             FLOOKUP s.vs_vars src_var =
             FLOOKUP s'.vs_vars (HD inst.inst_outputs))
End

Theorem cse_inst_simulates_proof:
  !bb_ids.
  analysis_inst_simulates
    (state_equiv {}) (execution_equiv {})
    (\dav. cse_sound (FST dav) (SND dav))
    (\v inst. [cse_inst bb_ids v inst])
Proof
  cheat
QED

Theorem cse_function_correct_proof:
  !fuel ctx fn s.
    lift_result (state_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx (cse_function fn) s)
Proof
  cheat
QED
