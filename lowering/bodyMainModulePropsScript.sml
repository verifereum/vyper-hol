(* Main-module code and support within a linked compiler unit. *)
Theory bodyMainModuleProps
Ancestors
  bodyInvSplit compileUnit alist

Theorem contract_inv_main_module:
  contract_inv mods exps ctx cenv cx ==>
  ALOOKUP mods NONE = SOME (main_module mods)
Proof
  Cases_on `ALOOKUP mods NONE` >> simp[contract_inv_def, main_module_def]
QED
