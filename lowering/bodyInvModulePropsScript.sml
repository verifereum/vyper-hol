Theory bodyInvModuleProps
Ancestors
  bodyInvSplit

Theorem module_body_inv_lookup:
  module_body_inv mods src tops cenv cx ==> ALOOKUP mods src = SOME tops
Proof
  simp[module_body_inv_def]
QED
