Theory makeSsaCurrentScanOrigin
Ancestors
  makeSsaCurrentTokens list

Theorem current_output_token_origin:
  !xs k t. current_output_token v l i k xs t = t \/
    ?j. j < LENGTH xs /\ EL j xs = v /\
        current_output_token v l i k xs t = CurrentOriginal l i (k + j)
Proof
  Induct >> simp[current_output_token_def] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`SUC k`,
    `if h = v then CurrentOriginal l i k else t`] strip_assume_tac)
  >- (Cases_on `h = v` >> gvs[] >> disj2_tac >>
      qexists_tac `0` >> simp[])
  >> disj2_tac >> qexists_tac `SUC j` >> simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem current_original_scan_origin:
  !insts i t. current_original_scan v l i insts t = t \/
    ?j k. j < LENGTH insts /\
      k < LENGTH (EL j insts).inst_outputs /\
      EL k (EL j insts).inst_outputs = v /\
      current_original_scan v l i insts t = CurrentOriginal l (i + j) k
Proof
  Induct >> simp[current_original_scan_def] >> rpt gen_tac >>
  first_x_assum (qspecl_then [`SUC i`,
    `current_output_token v l i 0 h.inst_outputs t`] strip_assume_tac)
  >- (`current_output_token v l i 0 h.inst_outputs t = t \/
       ?k. k < LENGTH h.inst_outputs /\ EL k h.inst_outputs = v /\
         current_output_token v l i 0 h.inst_outputs t = CurrentOriginal l i k`
        by metis_tac[current_output_token_origin, arithmeticTheory.ADD_CLAUSES]
      >- simp[] >> disj2_tac >> qexistsl_tac [`0`, `k`] >> simp[])
  >> disj2_tac >> qexistsl_tac [`SUC j`, `k`] >> simp[arithmeticTheory.ADD_CLAUSES]
QED
