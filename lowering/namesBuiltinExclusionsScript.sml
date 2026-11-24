Theory namesBuiltinExclusions
Ancestors
  exprSimHypsDefs vyperAST

Theorem names_builtin_exclusions:
  (!n args. ~names_builtin (Concat n) args) /\
  (!args. ~names_builtin NamedConst args)
Proof
  `!bt args. names_builtin bt args ==> bt <> NamedConst /\ (!n. bt <> Concat n)`
    suffices_by metis_tac[] >>
  ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]
QED
