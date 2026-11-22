(* The interpreter installs exactly the checker's ordered constant fold. *)
Theory vyperLinkedConstantInstall
Ancestors
  list option alist vyperInterpreter vyperTypeContract
  vyperTypeConstantCells vyperTypeConstantFold

Theorem checked_constants_installed_fold:
  check_contract mode layouts addr mods = SOME art /\
  initial_immutables (type_env_all_modules mods) mods = SOME init /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP am.immutables cx.txn.target = SOME init /\
  evaluate_all_constants cx am cx.txn.target mods = SOME am_c ==>
  ?last.
    constants_fold mods init (constants_order mods) = SOME last /\
    ALOOKUP am_c.immutables cx.txn.target = SOME last
Proof
  strip_tac >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def] >> rw[]) >>
  gvs[contract_constants_ok_def, IS_SOME_EXISTS, evaluate_all_constants_def] >>
  `deployment_constant_cells_typed (type_env_all_modules mods) cx.txn.target mods am` by
    (rw[deployment_constant_cells_typed_def] >>
     drule_all checked_initial_immutables_constant_absent >> gvs[]) >>
  drule_at (Pat `check_contract _ _ _ _ = _`) constants_fold_evaluate_module_constants >>
  disch_then (qspec_then `constants_order mods` mp_tac) >>
  simp[EVERY_MEM, MEM_constants_order] >> disch_then drule_all >>
  strip_tac >> gvs[]
QED
