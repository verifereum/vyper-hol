Theory whitelistAllocatedHeaderProps
Ancestors
  vyperAST vyperTypeContract e2eDefs alist pair option

Theorem layouts_agree_allocated_header:
  layouts_agree tops am tx /\ MEM tl tops /\
  toplevel_allocated am.layouts tx.target NONE tl ==>
  case tl of
    VariableDecl _ Storage _ _ slot => IS_SOME slot
  | VariableDecl _ Transient _ _ slot => IS_SOME slot
  | HashMapDecl _ _ _ _ _ slot => IS_SOME slot
  | _ => T
Proof
  Cases_on `tl` >> simp[] >>
  TRY (rename1 `VariableDecl _ mut` >> Cases_on `mut`) >>
  simp[toplevel_allocated_def, layouts_agree_def, lookup_var_slot_in_layouts_def] >>
  Cases_on `ALOOKUP am.layouts tx.target` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  metis_tac[]
QED
