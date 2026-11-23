Theory bodyInvMetadataProps
Ancestors
  bodyInvSplit vyperContext

Theorem contract_inv_type_env:
  contract_inv mods exps ctx cenv cx ==>
  get_tenv cx = type_env_all_modules mods
Proof
  simp[contract_inv_def, get_tenv_def]
QED

Theorem contract_inv_constructor:
  contract_inv mods exps ctx cenv cx ==>
  (cenv.ce_is_ctor <=> cx.in_deploy)
Proof
  simp[contract_inv_def]
QED
