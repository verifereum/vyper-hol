Theory moduleVariableKeyProps
Ancestors bodyInvSplit vyperTypeContract list pair

Theorem variable_keys_requalify[local]:
  !tops (src:num option).
    FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops) =
    MAP (\(key,id). (NONE,id))
      (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops))
Proof
  Induct >> simp[] >> Cases >>
  simp[toplevel_vtype_keys_toplevel_def]
QED

Theorem variable_keys_have_source[local]:
  !tops src key id.
    MEM (key,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) tops)) ==> key = src
Proof
  Induct >> simp[] >> Cases >> simp[toplevel_vtype_keys_toplevel_def] >>
  metis_tac[]
QED

Theorem module_variable_keys_unqualified:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (src:num option)) tops)) ==>
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  strip_tac >>
  ONCE_REWRITE_TAC [Q.SPECL [`tops`,`src`] variable_keys_requalify] >>
  irule ALL_DISTINCT_MAP_INJ >> simp[FORALL_PROD] >>
  metis_tac[variable_keys_have_source]
QED

Theorem contract_inv_unqualified_variable_keys:
  contract_inv mods exps ctx cenv cx ==>
  !src tops. ALOOKUP mods src = SOME tops ==>
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops))
Proof
  rw[contract_inv_def] >>
  metis_tac[module_variable_keys_unqualified]
QED
