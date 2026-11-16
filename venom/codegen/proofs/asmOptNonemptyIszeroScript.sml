Theory asmOptNonemptyIszero
Ancestors
  asmOptimizer asmOptNonemptyJumps

Theorem merge_iszero_pairs_trailing:
  !p. (?pre t post. p = pre ++ [t] ++ post /\ asm_terminal_op t /\
         EVERY (\i. !l. i <> AsmLabel l) post) ==>
      (?pre t post. FST (merge_iszero_pairs p) = pre ++ [t] ++ post /\
         asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  recInduct merge_iszero_pairs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[Once merge_iszero_pairs_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      IF_CASES_TAC
      >- (gvs[trailing_terminal_cons] >> metis_tac[])
      >> gvs[] >>
      mp_tac (Q.SPEC `y::z::rest` merge_iszero_pairs_no_labels) >>
      gvs[trailing_terminal_cons] >> metis_tac[])
  >> simp[merge_iszero_pairs_def]
QED

Theorem merge_iszero_jumpi_trailing:
  !p. (?pre t post. p = pre ++ [t] ++ post /\ asm_terminal_op t /\
         EVERY (\i. !l. i <> AsmLabel l) post) ==>
      (?pre t post. FST (merge_iszero_jumpi p) = pre ++ [t] ++ post /\
         asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  recInduct merge_iszero_jumpi_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      simp[Once merge_iszero_jumpi_def] >>
      rpt (pairarg_tac >> gvs[]) >>
      IF_CASES_TAC
      >- (gvs[trailing_terminal_cons] >> metis_tac[])
      >> gvs[] >>
      mp_tac (Q.SPEC `b::c::d::rest` merge_iszero_jumpi_no_labels) >>
      gvs[trailing_terminal_cons] >> metis_tac[])
  >> simp[merge_iszero_jumpi_def]
QED

Theorem merge_iszero_trailing:
  (?pre t post. p = pre ++ [t] ++ post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post) ==>
  (?pre t post. FST (merge_iszero p) = pre ++ [t] ++ post /\
     asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  simp[merge_iszero_def] >> rpt (pairarg_tac >> gvs[]) >>
  mp_tac (Q.SPEC `p` merge_iszero_pairs_trailing) >> simp[] >>
  mp_tac (Q.SPEC `asm1` merge_iszero_jumpi_trailing) >> simp[] >>
  metis_tac[]
QED
