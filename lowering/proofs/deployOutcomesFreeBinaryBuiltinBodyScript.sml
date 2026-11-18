Theory deployOutcomesFreeBinaryBuiltinBody
Ancestors
  deployOutcomesFreeSelectors deployOutcomesFreeExprBody
  deployOutcomesFreeGenerators exprLowering list

Theorem outcomes_free_literal_or_hash:
  (!st. Q st ==> Q (SND (lower_value f ce ity e st))) /\
  (!v st. Q st ==> Q (SND (compile_bytestring_hash v st))) /\ Q s ==>
  Q (SND (case bytestring_literal_hash e of
    SOME h => (Lit h, s)
  | NONE => (\(m, st). compile_bytestring_hash m st)
              (lower_value f ce ity e s)))
Proof
  strip_tac >> Cases_on `bytestring_literal_hash e` >> simp[] >>
  pairarg_tac >> simp[] >> metis_tac[pairTheory.SND]
QED
