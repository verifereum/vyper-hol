open HolKernel boolLib bossLib Parse;
open vyperTypeSoundnessDefsTheory;

val _ = new_theory "vyperTypeErrorCounterexample";

(* This theory previously contained a counterexample showing that the
   no-TypeError conjunct of the type soundness theorem was FALSE under
   the old (pre-strengthening) definitions. Specifically, TopLevelName NoneT
   was well-typed under the old definitions but materialise(HashMapRef)
   always raises TypeError.

   After the definition strengthening (adding ty <> NoneT to TopLevelName
   in well_typed_expr), this counterexample is no longer valid.
   The theory is kept as a placeholder since other files may reference it.
 *)

val _ = export_theory();
