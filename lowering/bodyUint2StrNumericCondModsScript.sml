Theory bodyUint2StrNumericCondMods

Theorem u2s_cond_specialize_mods:
  !P Q x str s G tn.
    (!x str s G tn. P x str s G tn ==> Q x str s G tn) /\
    P x str s G tn ==> Q x str s G tn
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `!x str s G tn. P x str s G tn ==> Q x str s G tn`
    (qspecl_then [`x`, `str`, `s`, `G`, `tn`] mp_tac) >>
  simp[]
QED
