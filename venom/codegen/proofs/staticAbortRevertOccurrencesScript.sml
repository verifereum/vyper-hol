(* Consecutive pre/emit/post occurrence indices, ending at the final emit. *)
Theory staticAbortRevertOccurrences
Ancestors arithmetic

Theorem revert_occurrence_cases:
  !k j i:num. 3*k <= i /\ i <= 3*j+1 ==>
    (?q. k <= q /\ q <= j /\ i = 3*q) \/
    (?q. k <= q /\ q <= j /\ i = 3*q+1) \/
    (?q. k <= q /\ q < j /\ i = 3*q+2)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPEC `i` (SIMP_RULE std_ss [] (Q.SPEC `3` DIVISION))) >>
  strip_tac >>
  `i MOD 3 < 3` by simp[MOD_LESS] >>
  `i MOD 3 = 0 \/ i MOD 3 = 1 \/ i MOD 3 = 2` by decide_tac
  >- (disj1_tac >> qexists `i DIV 3` >> decide_tac)
  >- (disj2_tac >> disj1_tac >> qexists `i DIV 3` >> decide_tac) >>
  disj2_tac >> disj2_tac >> qexists `i DIV 3` >> decide_tac
QED

Theorem revert_occurrence_decode:
  !q:num. ((3*q) DIV 3 = q /\ (3*q) MOD 3 = 0) /\
          ((3*q+1) DIV 3 = q /\ (3*q+1) MOD 3 = 1) /\
          ((3*q+2) DIV 3 = q /\ (3*q+2) MOD 3 = 2)
Proof
  gen_tac >>
  `3*q = q*3 /\ 3*q+1 = q*3+1 /\ 3*q+2 = q*3+2` by decide_tac >>
  ASM_SIMP_TAC std_ss [Q.SPECL [`3`,`0`] DIV_MULT,
    Q.SPECL [`3`,`1`] DIV_MULT, Q.SPECL [`3`,`2`] DIV_MULT,
    Q.SPECL [`3`,`0`] MOD_MULT, Q.SPECL [`3`,`1`] MOD_MULT,
    Q.SPECL [`3`,`2`] MOD_MULT,
    SIMP_RULE std_ss [ADD_CLAUSES] (Q.SPECL [`3`,`0`] DIV_MULT),
    SIMP_RULE std_ss [ADD_CLAUSES] (Q.SPECL [`3`,`0`] MOD_MULT)]
QED

Theorem revert_flatten_occurrences:
  k <= j /\
  (!q. k <= q /\ q <= j ==>
    P (pc q) (a q) (A q) F /\
    P (pc q + a q) (b q) (B q) (q = j) /\
    B q 0 = A q (a q)) /\
  (!q. k <= q /\ q < j ==>
    P (pc q + a q + b q) (c q) (C q) F /\
    C q 0 = B q (b q) /\ A (SUC q) 0 = C q (c q) /\
    pc (SUC q) = pc q + a q + b q + c q) ==>
  ?(base:num->num) (len:num->num) H.
    base (3*k) = pc k /\ H (3*k) 0 = A k 0 /\ len (3*j+1) = b j /\
    (!i. 3*k <= i /\ i <= 3*j+1 ==> P (base i) (len i) (H i) (i = 3*j+1)) /\
    (!i. 3*k <= i /\ i < 3*j+1 ==>
       base (SUC i) = base i + len i /\ H (SUC i) 0 = H i (len i))
Proof
  strip_tac >>
  qexistsl [`\i. let q = i DIV 3 in
                 if i MOD 3 = 0 then pc q
                 else if i MOD 3 = 1 then pc q + a q else pc q + a q + b q`,
            `\i. if i MOD 3 = 0 then a (i DIV 3)
                 else if i MOD 3 = 1 then b (i DIV 3) else c (i DIV 3)`,
            `\i. if i MOD 3 = 0 then A (i DIV 3)
                 else if i MOD 3 = 1 then B (i DIV 3) else C (i DIV 3)`] >>
  simp[revert_occurrence_decode] >> conj_tac
  >- (qx_gen_tac `i` >> disch_tac >>
      qspecl_then [`k`,`j`,`i`] mp_tac revert_occurrence_cases >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac
      >- (`3*q <> 3*j+1` by decide_tac >> simp[revert_occurrence_decode])
      >- ((`(3*q+1 = 3*j+1) <=> (q=j)` by decide_tac >>
          `a q + pc q = pc q + a q` by decide_tac >>
          pure_asm_rewrite_tac [revert_occurrence_decode] >>
          simp[revert_occurrence_decode] >> (gvs[revert_occurrence_decode]))) >>
      `3*q+2 <> 3*j+1` by decide_tac >>
      simp[revert_occurrence_decode] >>
      qpat_assum `!q. k <= q /\ q < j ==> _` (qspec_then `q` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `a q + (b q + pc q) = pc q + a q + b q` by decide_tac >>
      pure_asm_rewrite_tac []) >>
  qx_gen_tac `i` >> strip_tac >>
  qspecl_then [`k`,`j`,`i`] mp_tac revert_occurrence_cases >>
  (impl_tac >- decide_tac) >> strip_tac
  >- (`SUC (3*q) = 3*q+1` by decide_tac >>
      qpat_assum `!q. k <= q /\ q <= j ==> _` (qspec_then `q` mp_tac) >>
      simp[revert_occurrence_decode])
  >- (`q < j /\ SUC (3*q+1) = 3*q+2` by decide_tac >>
      qpat_assum `!q. k <= q /\ q < j ==> _` (qspec_then `q` mp_tac) >>
      simp[revert_occurrence_decode]) >>
  `SUC (3*q+2) = 3*SUC q` by decide_tac >>
  qpat_assum `!q. k <= q /\ q < j ==> _` (qspec_then `q` mp_tac) >>
  simp[revert_occurrence_decode]
QED
