(* The residual tuple assignments of bodySimStmtCases' body_assign_tuple_other:
   the element shapes left once body_assign_tuple_locals and
   body_assign_tuple_targets have taken theirs.
   TOP-LEVEL: assign_tuple_other_shapes. *)
Theory bodyAssignTupleOther
Ancestors
  exprSimAggregateLayout exprSimHypsDefs bodyStorageMetadata
  supportedStmts supportedDecls vyperTypeSystem vyperTypeInvariants vyperTypeEnv
  list finite_map

(* A supported, typed tuple assignment with an element outside
   body_assign_tuple_targets' (a local of nonzero size, a word scalar, a word
   field of a storage struct) has an element of one of three kinds: an
   immutable assigned in the constructor, an element of a storage array or
   mapping, or a storage struct field that is not a word.  A local's size is
   positive since its type is a tuple element's, which is assignable; an
   immutable is no assignable place outside the constructor. *)
Theorem assign_tuple_other_shapes:
  !cx gs e tops bindings cenv env ret_ty env' es.
    get_module_code cx NONE = SOME tops /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    ~EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                         FLOOKUP env.var_types id = SOME ty /\
                         0 < type_memory_bytes cenv ty) \/
                (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                        supported_scalar_target tops nsid) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env
                     (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ is_word_type fty)) gs ==>
    EXISTS (\g. (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                        cx.in_deploy /\
                        IS_SOME (supported_immutable_type tops nsid)) \/
                (?nsid key.
                   g = BaseTarget (SubscriptTarget (TopLevelNameTarget nsid) key) /\
                   supported_subscript_base tops nsid /\ supported_expr tops key) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env
                     (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ ~is_word_type fty)) gs
Proof
  rpt strip_tac >>
  gvs[NOT_EVERY, EXISTS_MEM] >> rename1 `MEM g gs` >>
  qexists_tac `g` >> simp[] >>
  `?tys. LIST_REL (\tgt ty. well_typed_atarget env tgt ty) gs tys /\
         assignable_type env.type_defs (TupleT tys)` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
         AllCaseEqs()] >> metis_tac[]) >>
  `?ty. well_typed_atarget env g ty /\ assignable_type env.type_defs ty` by
    (drule_all LIST_REL_MEM_IMP >> strip_tac >>
     gvs[assignable_type_def, EVERY_MEM] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx /\
   bare_globals_complete env.bare_globals cx /\
   bare_global_assignable_complete env.bare_global_assignable cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?bt. g = BaseTarget bt /\ supported_target tops bindings bt` by
    (gvs[supported_stmt_def, supported_assignment_def, EVERY_MEM] >>
     first_x_assum drule >> Cases_on `g` >> simp[]) >>
  gvs[well_typed_atarget_def, well_typed_target_def] >>
  Cases_on `bt` >> gvs[supported_target_def]
  >~ [`NameTarget id`]
  >- (gvs[type_place_target_NameTarget] >>
      drule_all expr_sim_inv_memory_bytes_pos >> simp[])
  >~ [`TopLevelNameTarget nsid`]
  >- (CCONTR_TAC >> gvs[] >>
      gvs[optionTheory.IS_SOME_EXISTS, supported_immutable_type_def,
          AllCaseEqs()] >>
      PairCases_on `nsid` >> drule supported_variable_decl_mem >> strip_tac >>
      gvs[bare_globals_complete_def, bare_global_assignable_complete_def] >>
      first_x_assum (drule_then drule) >> strip_tac >>
      qpat_x_assum `type_place_target _ _ = _` mp_tac >>
      simp[Once well_typed_expr_def])
  >~ [`SubscriptTarget t key`]
  >- (Cases_on `t` >> gvs[])
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[] >> metis_tac[])
QED
