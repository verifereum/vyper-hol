(* Declared immutable types control the footprint of stored immutables. *)
Theory internalReturnImmutableTypes
Ancestors
  bodyMemoryDefs immutableLocationProps bodyStorageMetadata
  vyperTypeInvariants bodySim exprSimHypsDefs vyperState
  bodyInvSplit bodyInvCodeProps immutableRegionTypingProps

Theorem internal_return_immutable_separation_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\ env_consistent env cx ee /\
  (!nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) b cap) ==>
  !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) b cap
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?bytes. immutable_region_mods mods cenv.ce_module name off bytes` by metis_tac[] >>
  drule_all_then strip_assume_tac immutable_region_mods_type >>
  `evaluate_type (get_tenv cx) ty = SOME itv` by
    (qpat_assum `env_consistent env cx ee`
       (mp_tac o cj 3 o REWRITE_RULE [env_consistent_def]) >>
     simp[env_immutables_consistent_def] >>
     disch_then (mp_tac o Q.SPECL [`cenv.ce_module`,`name`,`ty`,`itv`,`iv`] o cj 2) >>
     Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[]) >>
  metis_tac[]
QED

Theorem internal_return_immutable_separation:
  body_inv tops ctx cenv cx /\ cenv.ce_module = NONE /\
  cenv.ce_module_vars =
    add_immutable_locations (get_struct_fields (make_struct_fields_map tops))
      tops 0 (add_module_var_locations tops FEMPTY) /\
  expr_sim_inv cenv cx env es /\ env_consistent env cx ee /\
  cenv.ce_is_ctor /\
  (!nm io ity itv.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc io) /\
    cenv.ce_module_var_type (cenv.ce_module,nm) = SOME ity /\
    evaluate_type (get_tenv cx) ity = SOME itv ==>
    regions_disjoint io (type_memory_size itv) b cap) ==>
  !name itv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) =
      SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name =
      SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) b cap
Proof
  strip_tac >> drule_then strip_assume_tac body_inv_main_code >>
  drule_then assume_tac body_inv_contract >>
  fs[expr_sim_inv_split_def] >> metis_tac[internal_return_immutable_separation_mods]
QED
