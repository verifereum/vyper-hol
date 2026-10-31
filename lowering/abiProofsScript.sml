(* Build the standalone ABI correctness results alongside the caller proofs.
   These families include useful lemmas beyond the current lowering consumers. *)
Theory abiProofs
Ancestors
  (* Descriptor, physical-scratch and source-value encoding. *)
  abiEncoderCorrectArray abiEncoderCorrectComplex
  abiEncoderFragmentBridge abiEncoderLeafSafety
  abiScratchEncoderArray abiScratchEncoderComplex
  (* Canonical and actual-source decoding. *)
  abiDecoderCanonicalBound abiDecoderNestedArrayLoop
  abiDecoderReadabilityBoundary abiDecoderSingletonBulk
  abiDecoderStatic abiDecoderUnwrapExecute abiScratchDecoderIndex
  (* Builtins, empty values and caller inputs. *)
  abiBuiltinFlatChecks abiBuiltinHeaderReach abiBuiltinValidCaller
  abiEmptyDispatch abiScratchBuiltinProducer abiScratchDecodeHistoryCaller
  abiCallerArrayUnwrap abiCallerLocalScratch abiValidBytesCaller abiValidStructMembers
