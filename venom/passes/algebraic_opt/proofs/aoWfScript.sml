(* Algebraic Optimization — Well-formedness & SSA Preservation
 *
 * This file re-exports theorems from per-phase WF files for
 * backward compatibility. New code should import the per-phase
 * theories directly.
 *
 * Per-phase files:
 *   phase_1/aoPhase1WfScript.sml — phase 1 (offset conversion)
 *   phase_3/aoPhase3WfScript.sml — phase 3 (main rewrite)
 *   phase_4/aoPhase4WfScript.sml — phase 4 (cmp flip)
 *   shared/aoPreservationScript.sml — top-level composition
 *)

Theory aoWf
Ancestors
  aoPreservation
Libs
  BasicProvers

val _ = export_theory();
