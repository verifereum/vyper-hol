(* Baseline parser audit: ancestors intentionally match the original target. *)
Theory concretizePtrUniversalExtensionIdentity
Ancestors
  concretizePtrAffineFamily concretizePtrComparisonFamily concretizePtrIloadFamily concretizePtrByteStoreFamily concretizePtrBufferCopyFamily concretizePtrExtcodecopyFamily concretizePtrStorageWriteFamily concretizePtrHashLogFamily concretizePtrCallFamily concretizePtrCreateFamily
  concretizePtrStorageReadProducer

Theorem baseline_retpc_parse[local]:
  retpc_shape_ok = frameRel$retpc_shape_ok
Proof
  simp[]
QED

val _ = app (fn (label,th,expected) =>
  if List.all (fn c => #Thy (dest_thy_const c) = expected)
    (find_terms (fn c => is_const c andalso
      #Name (dest_thy_const c) = "retpc_shape_ok") (concl th))
  then print (label ^ ": " ^ expected ^ "$retpc_shape_ok\n")
  else raise Fail (label ^ ": unexpected retpc predicate"))
  [("JUMP",concretizePtrPairedJumpTheory.ptr_paired_jump_prefix_normalize,"unitShapeDefs"),
   ("STORAGE",concretizePtrStorageReadProducerTheory.ptr_paired_storage_read_prefix_normalize,"frameRel")];

Theorem source_shape_supplies_jump_retpc[local]:
  o1_ctx_shape C /\ MEM f C.ctx_functions ==>
  unitShapeDefs$retpc_shape_ok f
Proof
  simp[o1PassContractTheory.o1_ctx_shape_def,
       o1PassContractTheory.o1_fn_shape_def,
       unitShapeDefsTheory.fn_shape_ok_def, listTheory.EVERY_MEM] >> metis_tac[]
QED
