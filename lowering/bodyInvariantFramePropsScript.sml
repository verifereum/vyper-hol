(* Declaring a local preserves the unit and module metadata. *)
Theory bodyInvariantFrameProps
Ancestors
  bodySim bodyInvSplit compileEnv

Theorem body_invariants_same_frame:
  same_frame cenv c ==>
  (contract_inv mods exps ctx c cx <=> contract_inv mods exps ctx cenv cx) /\
  (module_body_inv mods src tops c cx <=> module_body_inv mods src tops cenv cx) /\
  (cenv_module_pins tops c <=> cenv_module_pins tops cenv)
Proof
  rw[same_frame_def] >>
  qpat_x_assum `_ = cenv` (SUBST1_TAC o SYM) >>
  simp[contract_inv_def, module_body_inv_def, cenv_module_pins_split_def,
       cenv_module_pins_mods_def, immutable_section_layout_mods_def,
       loweringStateRelDefsTheory.regions_disjoint_def]
QED
