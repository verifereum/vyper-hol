Theory bodyPtrBopInPair
Ancestors pair

Theorem pair_ignore_first:
  !p f. (\(x,s). f s) p = f (SND p)
Proof
  Cases >> simp[]
QED
