(* Source-side immutable update boundaries. *)
Theory immutableDeployAssignSourceFrame
Ancestors
  immutableDeployAssignSourceProbes exprSimHypsDefs vyperPlaceFrames vyperState
  vyperTypeInvariants alist finite_map

Theorem immutable_assign_source_lookup:
  expr_sim_inv ce cx env es /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?mods old. ALOOKUP es.immutables cx.txn.target = SOME mods /\
    FLOOKUP (get_source_immutables src mods) id = SOME (tv,old)
Proof
  strip_tac >>
  `env_immutables_consistent env cx es` by
    fs[expr_sim_inv_def, env_consistent_def] >>
  fs[env_immutables_consistent_def] >>
  first_assum (drule_then assume_tac) >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  metis_tac[optionTheory.IS_SOME_EXISTS, pairTheory.pair_CASES]
QED

Theorem immutable_root_write_lookup:
  ALOOKUP es.immutables cx.txn.target = SOME mods /\
  FLOOKUP (get_source_immutables src mods) id = SOME (tv,old) /\
  write_place cx (ImmutablePlace src id []) v es = (INL (),es') ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP es'.immutables cx.txn.target of
       NONE => [] | SOME m => m)) name =
  if name = id then SOME (tv,v)
  else FLOOKUP (get_source_immutables src mods) name
Proof
  strip_tac >>
  `get_immutables cx src es =
     (INL (get_source_immutables src mods),es)` by
    simp[get_immutables_def, get_address_immutables_def,
         lift_option_type_def, bind_def, return_def] >>
  drule_all immutable_root_write_set >>
  strip_tac >>
  gvs[set_immutable_def, get_address_immutables_def, lift_option_type_def,
      bind_def, return_def, set_address_immutables_def,
      set_source_immutables_def, get_source_immutables_def,
      FLOOKUP_UPDATE] >>
  metis_tac[]
QED
