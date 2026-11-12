Theory fmpStageFmpStepsRetCaller
Ancestors
  fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLedgerProps livenessProofs ptrDiscipline
  o1PassContract venomExecSemantics venomState venomInst rich_list

(* The saved target frame is already past the current point's restore. *)
Theorem fmp_return_tidx_suc:
  (EL idx insts).inst_opcode <> DALLOCA /\
  (!rl rp. root = SOME (rl,rp) /\ lbl = rl ==> rp <> SUC idx) ==>
  fmp_stage_tidx plan root lbl insts (SUC idx) =
    SUC (fmp_stage_tidx plan root lbl insts idx +
         (if (lbl,idx) IN FDOM plan then 1 else 0))
Proof
  strip_tac >> simp[fmp_stage_tidx_def, GENLIST, SUM_SNOC] >>
  Cases_on `root`
  >- (simp[] >> decide_tac) >>
  rename1 `SOME x` >> PairCases_on `x` >>
  simp[] >> rw[] >> fs[arithmeticTheory.ADD_CLAUSES]
QED
