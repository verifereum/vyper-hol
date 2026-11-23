Theory bodyInvExecutionProps
Ancestors
  bodyInvSplit bodyInvMetadataProps bodyInvCodeProps bodySim alist compileUnit
  vyperContext vyperTypeContract vyperABI

Theorem contract_inv_alloca_locals:
  contract_inv mods exps ctx cenv cx ==> cenv.ce_alloca_locals
Proof
  simp[contract_inv_def]
QED

Theorem contract_inv_return_types:
  contract_inv mods exps ctx cenv cx ==>
  cenv.ce_func_return_type = build_func_return_type_mods mods
Proof
  simp[contract_inv_def]
QED

Theorem body_inv_singleton_abi_types:
  body_inv tops ctx cenv cx /\ is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
  is_dynamic (vyper_to_abi_type (type_env tops) target)
Proof
  strip_tac >> drule_then assume_tac body_inv_contract >>
  drule_then assume_tac contract_inv_type_env >>
  fs[type_env_all_modules_def, type_env_def]
QED

Theorem contract_inv_supported_module:
  contract_inv mods exps ctx cenv cx /\ ALOOKUP mods NONE = SOME tops ==>
  supported_program tops
Proof
  rw[contract_inv_def] >> res_tac
QED

Theorem body_inv_main_support:
  body_inv tops ctx cenv cx ==>
  supported_program tops /\ get_module_code cx NONE = SOME tops
Proof
  strip_tac >>
  drule_then assume_tac body_inv_contract >>
  drule_then assume_tac body_inv_module >>
  metis_tac[contract_inv_module_gate, contract_inv_module_code]
QED
