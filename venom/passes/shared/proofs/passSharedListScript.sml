Theory passSharedList
Ancestors list

Theorem list_rel_flat:
  !R xss yss.
    LIST_REL (LIST_REL R) xss yss ==>
    LIST_REL R (FLAT xss) (FLAT yss)
Proof
  gen_tac >> Induct_on `xss` >> Cases_on `yss` >> simp[] >>
  rpt strip_tac >> irule LIST_REL_APPEND_suff >> simp[]
QED
