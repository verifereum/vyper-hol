(* Canonical checked scalar consumers share the successful scalar endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixScalar
Ancestors
  ctorDeployMemoryRunPtrPrefixScalarClamps ctorDeployMemoryRunPtrPrefixScalarPackage
  ctorDeployMemoryRunPtrPrefixCanonical ctorDeployMemoryRunPtrPrefixScalarBool
  abiEncoder abiDecoderContract abiDecoderClampedWord compileEnv exprLoweringProps
  venomState venomInst venomExecSemantics ptrDiscipline ptrSafeRun
  fragExec finite_map list rich_list words pred_set allocaFrontierBound





val _ = export_theory();
