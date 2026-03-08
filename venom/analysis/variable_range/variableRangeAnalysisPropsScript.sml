(*
 * Variable Range Analysis — Properties (public API)
 *
 * Consumer-facing soundness theorems. Consumers `Ancestors` this theory
 * to get defs + properties.
 *
 * TOP-LEVEL:
 *   range_analyze_block_sound   — block-level: entry sound ⇒ exit sound
 *   range_get_range_sound       — query: pre-inst state sound ⇒ range sound
 *)

Theory variableRangeAnalysisProps
Ancestors
  valueRangeDefs rangeEvalDefs rangeAnalysisDefs rangeAnalysisProofs

(* Block-level soundness of the analysis output: if the analysis's entry
   state for block lbl is sound for a concrete state s, and running the
   block from s succeeds, then the analysis's exit state is sound for
   the resulting concrete state.

   The consumer chains this along an execution path:
     entry_sound(lbl_0) → exit_sound(lbl_0) → entry_sound(lbl_1) → ... *)
Theorem range_analyze_block_sound:
  ∀fn fuel lbl bb s s'.
    let ra = range_analyze fn fuel in
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    lbl ∈ FDOM ra.ra_entry ∧
    in_range_state (range_entry_state ra lbl) s.vs_vars ∧
    run_block fuel' ctx bb s = OK s' ⇒
    in_range_state (range_exit_state ra lbl) s'.vs_vars
Proof
  cheat
QED

(* Query soundness: if the pre-instruction range state recorded by the
   analysis is sound for the concrete state, then the range returned
   by range_get_range contains the concrete operand value. *)
Theorem range_get_range_sound:
  ∀ra inst_id op w env.
    (∀rs. FLOOKUP ra.ra_inst inst_id = SOME rs ⇒
          in_range_state rs env) ∧
    (∀v. op = Var v ⇒ FLOOKUP env v = SOME w) ∧
    (∀v. op = Lit v ⇒ w = v) ⇒
    in_range (range_get_range ra op inst_id) w
Proof
  cheat
QED
