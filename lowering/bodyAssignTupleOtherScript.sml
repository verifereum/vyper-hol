(* The residual tuple assignments of bodySimStmtCases' body_assign_tuple_other:
   the element shapes left once body_assign_tuple_locals and
   body_assign_tuple_targets have taken theirs.  Every element is then a
   place outside an immutable, which stmtSimAssignTuplePlaces' root
   assigns, except two cases left admitted: an immutable assigned in the
   constructor, and an element of a storage array or mapping whose index is
   not pure.
   TOP-LEVEL: assign_tuple_other_shapes, body_assign_tuple_places;
   immutable_deploy_tuple_assign, tuple_assign_effectful_index (RESIDUAL). *)
Theory bodyAssignTupleOther
Ancestors
  stmtSimAssignTuplePlaces stmtSimAssignPlace targetPlaceSimCases targetPlaceSim bodySimExprCases
  bodyExprPreFacts bodySim
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

(* RESIDUAL: an immutable among the targets, assigned in the constructor.
   The lowering keeps it in code (LocCode), which nothing relates to the
   source's immutables yet (targetPlaceSim's immutable_root); it waits on a
   strengthening of immutable_alloca_sep and body_inv. *)
Theorem immutable_deploy_tuple_assign:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    EXISTS (\g. ?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                       cx.in_deploy /\
                       IS_SOME (supported_immutable_type tops nsid)) gs ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* RESIDUAL: an element of a storage array or mapping whose index is not
   pure, which may make an internal call between the stores (as
   exprSimPopNested's pop_nested_storage_effectful_sim). *)
Theorem tuple_assign_effectful_index:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    EXISTS (\g. ?nsid key.
                  g = BaseTarget (SubscriptTarget (TopLevelNameTarget nsid) key) /\
                  ~supported_pure_expr tops key) gs ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED

(* body_assign_tuple_other for an RHS lowered at its own type: the two
   residual cases, and otherwise every element is a place outside an
   immutable with pure indices, which compile_assign_tuple_places_stmt_frag
   assigns.  The last three premises are what bodySimStmtCases' local
   helpers give (body_inv_mcopy, body_assign_tuple_rhs_pre,
   tuple_staging_bound). *)
Theorem body_assign_tuple_places:
  !cx gs e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' tv t s'3' v t'.
       eval_expr cx e s'' = (INL tv,t) /\ read_result cx tv s'3' = (INL v,t') ==>
       body_tuple_target_ok cx (TupleTarget gs) v) /\ body_expr_ok cx e /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    lowered_value_type cenv e = expr_type e /\
    cenv.ce_target CapMcopy /\ expr_body_pre cenv cx env e es /\
    (!tys tvs. expr_type e = TupleT tys /\
       evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
       is_memory_view e ==>
       type_memory_size (TupleTV tvs) < dimword (:256)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (TupleTarget gs) e))
      (eval_stmt cx (Assign (TupleTarget gs) e)) es
Proof
  cheat
QED
