(* Exact finite compiler specialization; no runtime correctness is asserted. *)
Theory ctorDeployMemoryRunPtrPrefixBoolShape
Ancestors
  loweringStateRelDefs
  abiEncoder abiDecoderExecution context emitHelper compileEnv fragExec
  exprLoweringProps emitHelperProps words arithmetic list ASCIInumbers




(* Every generated variable is different, not merely adjacent temporaries. *)




(* fn_has_code covers all three finished blocks exactly. Its final partial
   exit block need only exist: it is not necessarily an empty function block. *)

val _ = export_theory();
