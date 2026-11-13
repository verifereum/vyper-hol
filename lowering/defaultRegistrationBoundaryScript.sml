(* Empty registration is the identity compiler computation. *)
Theory defaultRegistrationBoundary
Ancestors
  moduleLowering

Theorem default_registration_empty:
  compile_register_positional_args ce [] 4 st = (ce,st)
Proof
  simp[compile_register_positional_args_def, compileEnvTheory.comp_return_def]
QED
