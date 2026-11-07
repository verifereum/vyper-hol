Theory concretizePtrContentCompatibilityProbe
Ancestors concretizePtrTaintContent venomExecSemantics venomCallOracleDefs
  ptrDiscipline venomState venomMemProps finite_map words list

(* Bookkeeping is deliberately not the executable ILOAD source. *)
Theorem ptr_immutable_bookkeeping_not_memory_probe:
  FLOOKUP (mstore 0 2w (istore 0 1w (init_venom_state "entry"))).vs_immutables 0 = SOME 1w /\
  mload 0 (mstore 0 2w (istore 0 1w (init_venom_state "entry"))) = 2w
Proof simp[mload_mstore_same, istore_def, mstore_def, FLOOKUP_UPDATE]
QED
