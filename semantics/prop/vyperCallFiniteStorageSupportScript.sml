(* Shared boundary facts for whole-run finite storage preservation. *)
Theory vyperCallFiniteStorageSupport
Ancestors
  vyperStorageFootprint vyperStorageBackend vyperInterpreter vyperLookupStorage
  vyperStorage vyperState vfmProg vfmExecution vfmState

Theorem storage_well_formed_on_target:
  cx'.txn.target = cx.txn.target ==>
  (storage_well_formed_on cx' st regions <=>
   storage_well_formed_on cx st regions)
Proof
  strip_tac >>
  `!b. get_storage cx' st b = get_storage cx st b` by
    (Cases_on `b` >> simp[get_storage_def]) >>
  simp[storage_well_formed_on_def]
QED

