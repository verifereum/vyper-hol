(* The deployed constant cells agree with the checker's fold in every module. *)
Theory vyperDeployConstantsFoldMods
Ancestors
  vyperInterpreter vyperContext vyperState vyperTypeContract
  vyperTypeInvariants vyperTypeContractSoundness
  vyperLinkedConstantInstall vyperDeployConstantsFoldAssembly
  vyperLinkedConstructorFrames vyperLinkedConstantSlotReplay
  finite_map alist

Theorem load_contract_establishes_constants_fold_mods:
  load_contract orc gs am tx mods exps = INL (am', rqs) /\
  am'.sources <> am.sources /\
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  ALOOKUP mods NONE = SOME main /\ machine_well_typed am /\
  context_well_typed
    (initial_evaluation_context ((tx.target, mods) :: am.sources)
       am.layouts (tx with created_in_tx := T) NONE with in_deploy := T) ==>
  ?imms.
    ALOOKUP am'.immutables tx.target = SOME imms /\
    !src tops. MEM (src, tops) mods ==>
      ?cenv.
        constants_fold_module mods imms src tops FEMPTY = SOME cenv /\
        cenv SUBMAP get_source_immutables src imms
Proof
  strip_tac >>
  drule_all load_contract_success_constructor_constants_context >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `call_external_function orc gs am0 cx` >>
  `cx.in_deploy /\ cx.txn.target = tx.target /\ cx.layouts = am.layouts /\
   ALOOKUP cx.sources cx.txn.target = SOME mods` by
    simp[Abbr `cx`, initial_evaluation_context_def] >>
  `ALOOKUP am0.immutables cx.txn.target = SOME imms` by simp[Abbr `am0`] >>
  `evaluate_all_constants cx am0 cx.txn.target mods = SOME am_c` by simp[] >>
  drule_all checked_constants_installed_fold >> strip_tac >>
  `check_contract T cx.layouts cx.txn.target mods = SOME deploy_art` by simp[] >>
  `!sid nm. declared_constant mods sid nm ==>
    (!st r st'. eval_exprs cx (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) st =
      (r,st') ==> lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
    (!st r st'. eval_stmts cx body' st = (r,st') ==>
      lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm)` by
    (rpt gen_tac >> strip_tac >>
     drule_all checked_deploy_constructor_frames >> metis_tac[]) >>
  drule_all deploy_call_framed_constant_slot >> strip_tac >>
  qexists `dst` >> simp[] >>
  metis_tac[checked_ordered_fold_slot_replay]
QED
