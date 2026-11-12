Theory bodyPtrBytestringBuiltinsUintFrame
Ancestors exprSimUint2Str venomState

Theorem u2s_frame_halted:
  u2s_frame a b sz sr s ==> s.vs_halted = sr.vs_halted
Proof
  rewrite_tac[u2s_frame_def] >> strip_tac >>
  qpat_x_assum `_ = sr` (mp_tac o Q.AP_TERM `\z. z.vs_halted`) >> simp[]
QED

Theorem u2s_safe_halted:
  u2s_safe ctx fn cenv cx es a buf b sz inst sr s ==>
  s.vs_halted = sr.vs_halted
Proof
  rewrite_tac[u2s_safe_def] >> strip_tac >>
  drule u2s_frame_halted >> simp[]
QED
