Theory bodyLinkedUnqualifiedCallProps
Ancestors
  bodyCallSupport supportedProgram vyperTypeContract alist finite_map list pair
  compileUnit[qualified] vyperTypeContractStaticMaps[qualified]

(* Local support excludes the constructor's reserved name in every
   checked module. The qualified typing signature then selects an Internal
   declaration in the main module, even when the active module is imported. *)
Theorem checked_linked_unqualified_call:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP mods src = SOME tops /\
  IS_SOME (supported_function_decl tops (NONE,name) Internal) /\
  linked_fn_sigs_declared mods cx fn_sigs /\ (NONE,name) IN FDOM fn_sigs ==>
  IS_SOME (supported_function_decl (main_module mods) (NONE,name) Internal)
Proof
  strip_tac >>
  Cases_on `?ts. mods = [(NONE,ts)]`
  >- gvs[ALOOKUP_def, compileUnitTheory.main_module_def] >>
  `name <> "__init__"` by
    (qpat_x_assum `IS_SOME (supported_function_decl _ _ _)` mp_tac >>
     simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     rename1 `supported_function_decl _ _ _ = SOME decl` >>
     PairCases_on `decl` >>
     drule supported_internal_lookup >> strip_tac >>
     drule vyperTypeContractStaticMapsTheory.lookup_function_Internal_SOME_MEM >> strip_tac >>
     drule ALOOKUP_MEM >> strip_tac >>
     drule_all check_contract_function_header >> simp[function_header_ok_def]) >>
  `?sg. FLOOKUP fn_sigs (NONE,name) = SOME sg` by simp[FLOOKUP_DEF] >>
  pop_assum strip_assume_tac >>
  fs[linked_fn_sigs_declared_def] >> first_x_assum drule >> strip_tac >>
  `vis = Internal` by
    (drule ALOOKUP_MEM >> strip_tac >>
     drule_all check_contract_function_header >>
     Cases_on `vis` >> gvs[include_fn_sig_def, function_header_ok_def]) >>
  gvs[compileUnitTheory.main_module_def] >> irule supported_function_decl_exists >>
  goal_assum drule
QED
