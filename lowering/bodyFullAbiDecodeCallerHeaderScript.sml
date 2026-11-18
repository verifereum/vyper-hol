(* Joint execution of the finite caller header, before output allocation. *)
Theory bodyFullAbiDecodeCallerHeader
Ancestors
  bodyFullAbiDecodeInterface bodyFullAbiDecodeLeafCases
  abiBuiltinDecodeSetup
  exprSimAbiDecodeBuiltinHeader abiDecoderAbortReentry
  abiDecoderVarSequence exprSimAbiDecodeFreshProbe
  abiDecodePtrRead assignTuplePtrLocalBytesCopy
  bodyPtrBopScalarCompile bodyPtrBopScalarOutcome
  bodyFullAbiDecodePath instSeqPtrLo fragGasOriginPtrDead
  stateFrame words finite_map pred_set list rich_list

