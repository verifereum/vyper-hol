Theory bodyPtrPrecompileBuiltinsBounds
Ancestors ptrDiscipline arithmetic

Theorem allocas_from_zero[simp]:
  !s. allocas_from 0 s
Proof
  simp[allocas_from_def]
QED
