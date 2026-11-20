(* Build the standalone ABI correctness results alongside the caller proofs.
   These families include useful lemmas beyond the current lowering consumers. *)
Theory abiProofs
Ancestors
  (* Descriptor, physical-scratch and source-value encoding. *)
  (* Canonical and actual-source decoding. *)
  ctorAbiActual ctorArgDecode
  (* Builtins, empty values and caller inputs. *)
  abiBuiltinValidCaller
  abiEmptyDispatch
  abiCallerLocalScratch
