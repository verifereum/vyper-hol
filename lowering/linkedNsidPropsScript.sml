Theory linkedNsidProps
Ancestors
  compileEnv ASCIInumbers string rich_list list pair option

Theorem decimal_has_no_dot[local]:
  ~MEM #"." (toString n)
Proof
  `~isDigit #"."` by EVAL_TAC >>
  mp_tac (Q.SPEC `n` EVERY_isDigit_num_to_dec_string) >>
  simp[EVERY_MEM] >>
  disch_then (qspec_then `#"."` mp_tac) >>
  simp[]
QED

Theorem decimal_dot_prefix[local]:
  FST (SPLITP (\c. c = #".") (toString n ++ #"." :: name)) =
  toString n
Proof
  simp[SPLITP_APPEND, EXISTS_MEM, decimal_has_no_dot, SPLITP]
QED

Theorem nsid_to_string_dot_free_injective:
  ~MEM #"." (SND a) /\ ~MEM #"." (SND b) /\
  nsid_to_string a = nsid_to_string b ==>
  a = b
Proof
  PairCases_on `a` >> PairCases_on `b` >>
  Cases_on `a0` >> Cases_on `b0` >>
  simp[nsid_to_string_def] >>
  rpt strip_tac >> gvs[MEM_APPEND]
  >- (qpat_assum `toString _ ++ _ = toString _ ++ _`
        (mp_tac o AP_TERM ``FST o SPLITP (\c. c = #".")``) >>
      simp[decimal_dot_prefix, toString_11] >>
      strip_tac >> gvs[APPEND_11])
QED
