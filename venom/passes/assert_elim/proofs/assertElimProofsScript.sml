(*
 * Assert Elimination — Proofs
 *
 * Key lemma: assert_elim_inst satisfies analysis_inst_simulates
 * with sound = in_range_state.
 * Lifting: df_analysis_pass_correct_widen_sound gives function-level result.
 *)

Theory assertElimProofs
Ancestors
  assertElimDefs analysisSimProps passSimulationProps

(* Soundness predicate: the range state at this point describes
   the concrete variable environment *)
Theorem assert_elim_inst_simulates_proof:
  analysis_inst_simulates
    (state_equiv {}) (execution_equiv {})
    (\rs_opt s. case rs_opt of
                  NONE => T
                | SOME rs => in_range_state rs s.vs_vars)
    (\v inst. [assert_elim_inst v inst])
Proof
  cheat
QED

Theorem assert_elim_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn /\ s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (assert_elim_function fn) s)
Proof
  cheat
QED
