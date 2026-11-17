(* Numerical boundary algorithms, independent of the frame relation. *)
Theory symFrameBoundaryNumeric
Ancestors
  codegenSymRel fnFrameSteps fnFrameSinglePred fnEntryParams fnFrameBoundary
  asmSymBridge asmSymSem frameRel contextCodegenRel codegenRel unitShapeDefs
  stackPlanGen stackPlanTypes planExec asmSem venomExecSemantics venomState
  venomInst dfgDefs symShuffleSim reorderStages codegenSymOwnRel

Theorem scratch_fold_outside:
  !xs labs b.
    EVERY (\p. ~in_mem_range (FST p) 32 b) xs ==>
    FLOOKUP (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) b = FLOOKUP labs b
Proof
  Induct >> simp[] >>
  Cases_on `h` >> simp[] >>
  metis_tac[scratch_store_labels_outside]
QED

Theorem scratch_fold_preserves_saved:
  !xs labs old saved.
    EVERY (\p. old + 32 <= FST p \/ FST p + 32 <= old) xs ==>
    (mem_sval_at (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) old saved <=>
     mem_sval_at labs old saved)
Proof
  Induct >> simp[] >>
  Cases_on `h` >> simp[] >>
  metis_tac[scratch_store_labels_preserves_saved]
QED

Theorem scratch_fold_saved:
  !xs labs.
    ALL_DISTINCT (MAP FST xs) /\
    (!p q. MEM p xs /\ MEM q xs /\ FST p <> FST q ==>
       FST p + 32 <= FST q \/ FST q + 32 <= FST p) ==>
    !off sv. MEM (off,sv) xs ==>
      mem_sval_at (FOLDL (\acc p. scratch_store_labels acc (FST p) (SND p)) labs xs) off sv
Proof
  Induct >> simp[] >>
  gen_tac >> PairCases_on `h` >> rw[]
  >- (gvs[] >> rename1 `~MEM off (MAP FST xs)` >>
      `EVERY (\p. off + 32 <= FST p \/ FST p + 32 <= off) xs` by
        (simp[listTheory.EVERY_MEM] >>
         metis_tac[listTheory.MEM_MAP, pairTheory.FST]) >>
      metis_tac[scratch_fold_preserves_saved, scratch_store_labels_at]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED
