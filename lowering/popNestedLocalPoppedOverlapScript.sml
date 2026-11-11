Theory popNestedLocalPoppedOverlap
Ancestors
  targetPlaceSim exprSimHypsDefs vyperSubscriptOverlap allocLimits stmtLowering

Theorem local_nonconstant_read[local]:
  !accs mods id.
    MEM (LocalRef id) (nonconstant_reads mods accs) <=>
    MEM (ReadAcc (LocalRef id)) accs
Proof
  Induct >> simp[nonconstant_reads_def] >>
  Cases_on `h` >> simp[nonconstant_reads_def] >>
  rename1 `ReadAcc v` >> Cases_on `v` >> simp[nonconstant_reads_def] >>
  PairCases_on `p` >> simp[nonconstant_reads_def] >>
  rpt gen_tac >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem local_target_root_read:
  !bt mods id. target_root bt = NameTarget id ==>
    MEM (LocalRef id)
      (nonconstant_reads mods (expr_accesses mods (target_to_expr bt)))
Proof
  qsuff_tac `!bt id. target_root bt = NameTarget id ==>
    MEM (ReadAcc (LocalRef id)) (accesses_expr (target_to_expr bt))`
  >- (simp[local_nonconstant_read, expr_accesses_def] >> metis_tac[]) >>
  gen_tac >> measureInduct_on `base_assignment_target_size bt` >>
  Cases_on `bt` >>
  simp[target_root_def, target_to_expr_def, accesses_expr_def]
QED

Theorem any_written_member[local]:
  !reads accs v. MEM v reads /\ MEM (WriteAcc v) accs ==>
    any_written reads accs
Proof
  Induct >> simp[any_written_def] >> metis_tac[]
QED

Theorem local_target_overlap_excludes_write:
  target_root bt = NameTarget id /\
  target_through_dynarray cenv bt /\
  ~target_subscript_overlap cenv bt idx ==>
  ~MEM (WriteAcc (LocalRef id)) (expr_accesses cenv.ce_modules idx) /\
  ~MEM RiskyAcc (expr_accesses cenv.ce_modules idx)
Proof
  rpt strip_tac >>
  `MEM (LocalRef id) (nonconstant_reads cenv.ce_modules
      (expr_accesses cenv.ce_modules (target_to_expr bt)))` by
    metis_tac[local_target_root_read] >>
  gvs[target_subscript_overlap_def] >>
  metis_tac[any_written_member, listTheory.MEM]
QED

Theorem pop_body_alloc_limits_target:
  expr_body_pre cenv cx env (Pop ann bt) es ==>
  alloc_limits_target cenv bt
Proof
  simp[expr_body_pre_def, alloc_limits_expr_def]
QED
