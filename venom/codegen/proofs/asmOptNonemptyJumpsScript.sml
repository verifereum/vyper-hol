Theory asmOptNonemptyJumps
Ancestors
  asmOptimizer

Theorem trailing_terminal_cons:
  (?pre t post. x::xs = pre ++ [t] ++ post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post) <=>
  (asm_terminal_op x /\ EVERY (\i. !l. i <> AsmLabel l) xs) \/
  (?pre t post. xs = pre ++ [t] ++ post /\ asm_terminal_op t /\
     EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  eq_tac
  >- (strip_tac >> Cases_on `pre` >> gvs[] >> metis_tac[])
  >> strip_tac
  >- (qexistsl [`[]`, `x`, `xs`] >> simp[])
  >> qexistsl [`x::pre`, `t`, `post`] >> simp[]
QED

Theorem nonterminal_items[simp]:
  ~asm_terminal_op (AsmOp "ISZERO") /\
  ~asm_terminal_op (AsmOp "JUMPI") /\
  ~asm_terminal_op (AsmPushLabel l) /\
  ~asm_terminal_op (AsmLabel l)
Proof
  simp[asm_terminal_op_def]
QED

Theorem trailing_terminal_zero_window[local]:
  (?pre t post. x::AsmOp "ISZERO"::AsmOp "ISZERO"::r = pre ++ [t] ++ post /\
    asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post) <=>
  (?pre t post. x::r = pre ++ [t] ++ post /\
    asm_terminal_op t /\ EVERY (\i. !l. i <> AsmLabel l) post)
Proof
  simp[trailing_terminal_cons]
QED

Theorem merge_iszero_pairs_no_labels:
  !p. EVERY (\i. !l. i <> AsmLabel l) p ==>
      EVERY (\i. !l. i <> AsmLabel l) (FST (merge_iszero_pairs p))
Proof
  recInduct merge_iszero_pairs_ind >> rpt strip_tac >>
  simp[Once merge_iszero_pairs_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[]
QED

Theorem merge_iszero_jumpi_no_labels:
  !p. EVERY (\i. !l. i <> AsmLabel l) p ==>
      EVERY (\i. !l. i <> AsmLabel l) (FST (merge_iszero_jumpi p))
Proof
  recInduct merge_iszero_jumpi_ind >> rpt strip_tac >>
  simp[Once merge_iszero_jumpi_def] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >> gvs[]
QED

Theorem prune_inefficient_jumps_no_labels:
  !p. EVERY (\i. !l. i <> AsmLabel l) p ==>
      EVERY (\i. !l. i <> AsmLabel l) (FST (prune_inefficient_jumps p))
Proof
  recInduct prune_inefficient_jumps_ind >> rpt strip_tac >>
  simp[Once prune_inefficient_jumps_def] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >> gvs[]
QED

Theorem optimize_inefficient_jumps_no_labels:
  !p. EVERY (\i. !l. i <> AsmLabel l) p ==>
      EVERY (\i. !l. i <> AsmLabel l) (FST (optimize_inefficient_jumps p))
Proof
  recInduct optimize_inefficient_jumps_ind >> rpt strip_tac >>
  simp[Once optimize_inefficient_jumps_def] >>
  rpt (pairarg_tac >> gvs[]) >> IF_CASES_TAC >> gvs[]
QED

Theorem trailing_terminal_cons_transport:
  (((?pre t post. p = pre ++ [t] ++ post /\ asm_terminal_op t /\
       EVERY (\i. !l. i <> AsmLabel l) post) ==>
    (?pre t post. q = pre ++ [t] ++ post /\ asm_terminal_op t /\
       EVERY (\i. !l. i <> AsmLabel l) post)) /\
   (EVERY (\i. !l. i <> AsmLabel l) p ==>
    EVERY (\i. !l. i <> AsmLabel l) q)) ==>
  ((?pre t post. x::p = pre ++ [t] ++ post /\ asm_terminal_op t /\
       EVERY (\i. !l. i <> AsmLabel l) post) ==>
   (?pre t post. x::q = pre ++ [t] ++ post /\ asm_terminal_op t /\
       EVERY (\i. !l. i <> AsmLabel l) post))
Proof
  simp[trailing_terminal_cons] >> metis_tac[]
QED
