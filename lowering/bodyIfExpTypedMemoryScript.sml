(* Typed normalization interfaces for conditional-arm memory consumers. *)
Theory bodyIfExpTypedMemory
Ancestors
  typedNormalizeEntryBoundary typedStoreEndpoint typedStorePathsMem exprSimMemUnwrap
  externalNormalizePremises externalReturnNormalizeRun exprSimIfExp
  context compileEnv venomExecSemantics venomInst emitHelper fragExec

(* Operational typed-store paths replace the unused assignment-entry shim. *)
