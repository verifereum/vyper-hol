(* TOP-LEVEL: exact membership of the two-external-function manifest fixture.
   Kept separate because evaluating the actual selector check is expensive. *)
Theory supportedFixturesMultiple
Ancestors supportedProgram evalCompiler
Libs supportedEvalLib

val () = supportedEvalLib.configure ();

Theorem two_external_supported_program:
  supported_program evalCompiler$two_external_program
Proof
  EVAL_TAC
QED
