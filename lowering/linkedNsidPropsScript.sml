Theory linkedNsidProps
Ancestors
  compileEnv ASCIInumbers string list pair option

Theorem decimal_has_no_dot[local]:
  ~MEM #"." (toString (n:num))
Proof
  `~isDigit #"."` by EVAL_TAC >>
  mp_tac (Q.SPEC `n` EVERY_isDigit_num_to_dec_string) >>
  simp[EVERY_MEM] >>
  disch_then (qspec_then `#"."` mp_tac) >>
  simp[]
QED

Theorem nsid_to_string_dot_free_injective:
  ~MEM #"." (SND a) /\ ~MEM #"." (SND b) /\
  nsid_to_string a = nsid_to_string b ==>
  a = b
Proof
  PairCases_on `a` >> PairCases_on `b` >>
  Cases_on `a0` >> Cases_on `b0` >>
  simp[nsid_to_string_def] >>
  rpt strip_tac >> gvs[MEM_APPEND] >>
  drule MEM_APPEND_lemma >>
  simp[decimal_has_no_dot, toString_11]
QED
