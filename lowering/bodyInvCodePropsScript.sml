Theory bodyInvCodeProps
Ancestors
  bodySim bodyInvSplit gasContext alist

Theorem contract_inv_module_codes:
  contract_inv mods exps ctx cenv cx ==>
  !src. get_module_code cx src = ALOOKUP mods src
Proof
  simp[contract_inv_def, vyperContextTheory.get_module_code_def]
QED

Theorem contract_inv_cenv_modules:
  contract_inv mods exps ctx cenv cx ==> cenv.ce_modules = mods
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def]
QED

Theorem body_inv_unit_immutable_layout:
  body_inv tops ctx cenv cx ==>
  immutable_section_layout_mods cenv.ce_modules cenv
Proof
  metis_tac[body_inv_contract, contract_inv_immutable_section_layout,
            contract_inv_cenv_modules]
QED

Theorem contract_inv_struct_fields:
  contract_inv mods exps ctx cenv cx ==>
  cenv.ce_struct_fields = make_struct_fields_map_mods mods
Proof
  simp[contract_inv_def]
QED

Theorem contract_inv_acyclic_struct_metadata:
  contract_inv mods exps ctx cenv cx ==> acyclic_struct_metadata cenv.ce_struct_fields
Proof
  simp[contract_inv_def]
QED

Theorem body_inv_main_code:
  body_inv tops ctx cenv cx ==>
  get_module_code cx NONE = SOME tops /\ cx_tops cx = tops
Proof
  strip_tac >>
  drule body_inv_contract >>
  disch_then (qspec_then `NONE` assume_tac o
    MATCH_MP contract_inv_module_codes) >>
  fs[ALOOKUP_def, cx_tops_module]
QED

Theorem body_inv_module_locations:
  body_inv tops ctx cenv cx ==>
  cenv.ce_module = NONE /\
  cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY)
Proof
  simp[body_inv_split_def, contract_inv_def, module_body_inv_def,
       cenv_module_pins_mods_def,
       compileUnitTheory.make_struct_fields_map_mods_singleton,
       compileUnitTheory.add_immutable_locations_unit_singleton,
       compileUnitTheory.add_module_var_locations_mods_singleton]
QED
