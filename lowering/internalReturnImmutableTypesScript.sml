(* Declared immutable types control the footprint of stored immutables. *)
Theory internalReturnImmutableTypes
Ancestors
  bodyMemoryDefs immutableLocationProps exprSimPopImmutableTarget
  vyperTypeInvariants compileVyper bodySim exprSimHypsDefs vyperState

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
  rpt strip_tac >>
  `?pre post vis ity slot.
     tops = pre ++ VariableDecl vis Immutable name ity slot :: post` by
    (qpat_x_assum `FLOOKUP cenv.ce_module_vars _ = _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >>
     drule immutable_locations_origin >> strip_tac
     >- (drule immutable_module_vars_origin >> simp[]) >>
     metis_tac[pairTheory.CLOSED_PAIR_EQ]) >>
  `MEM (VariableDecl vis Immutable name ity slot) tops` by simp[] >>
  `bare_global_assignable_complete env.bare_global_assignable cx /\
   env_immutables_consistent env cx ee` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `get_module_code cx NONE = SOME tops /\ cx.in_deploy` by
    fs[body_inv_def] >>
  `FLOOKUP env.bare_global_assignable (NONE,name) = SOME ity` by
    metis_tac[bare_global_assignable_complete_def] >>
  `FLOOKUP env.bare_globals (NONE,name) = SOME ity` by
    (fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
     metis_tac[bare_globals_complete_def]) >>
  `cenv.ce_module_var_type (NONE,name) = SOME ity` by
    (drule_all body_imm_var_type >> simp[]) >>
  `evaluate_type (get_tenv cx) ity = SOME itv` by
    (Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
     fs[env_immutables_consistent_def, get_source_immutables_def] >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED
