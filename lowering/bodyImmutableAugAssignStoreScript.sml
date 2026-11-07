Theory bodyImmutableAugAssignStore
Ancestors
  bodyImmutableAugAssignFacts bodySim exprSimHypsDefs compileEnv
  exprLoweringProps immutableConstructorRelation immutableMemoryFrame
  immutableEncoding immutableEncodingProofs immutableValue valueEncodingProps
  localPtrsProps vyperState vyperInterpreter vyperValueOperation
  finite_map alist list

Theorem immutable_augassign_write_source:
  ALOOKUP st.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (tv,old) ==>
  write_place cx (ImmutablePlace src id []) v st =
    (INL (), st with immutables :=
      (cx.txn.target, update_immutable src id tv v imms) ::
      ADELKEY cx.txn.target st.immutables)
Proof
  strip_tac >>
  simp[write_place_def, get_immutables_def, get_address_immutables_def,
       bind_def, return_def, lift_option_type_def, lift_sum_def,
       assign_subscripts_def, set_immutable_def, set_address_immutables_def,
       update_immutable_def, evaluation_state_component_equality]
QED

Theorem immutable_augassign_local_frame:
  stmt_state_rel ctx func cenv cx es ss /\ cenv.ce_is_ctor /\
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (cenv.ce_module,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ type_memory_size tv = 32 ==>
  local_ptrs_rel func cenv es.scopes (mstore off w ss)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes ss` by
    fs[stmt_state_rel_def, state_rel_def] >>
  irule local_ptrs_rel_mstore >> simp[] >>
  rpt strip_tac >>
  `immutable_decl_sep cenv cx es.scopes ss.vs_vars ss.vs_allocas
     ss.vs_alloca_next` by
    fs[stmt_state_rel_def, immutable_alloca_sep_def] >>
  fs[immutable_decl_sep_alt] >>
  first_x_assum drule_all >> strip_tac >>
  fs[regions_disjoint_def] >> metis_tac[]
QED
