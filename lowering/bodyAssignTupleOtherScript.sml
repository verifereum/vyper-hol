(* The residual tuple assignments of bodySimStmtCases' body_assign_tuple_other:
   the element shapes left once body_assign_tuple_locals and
   body_assign_tuple_targets have taken theirs.  Every element is then a
   place outside an immutable, which stmtSimAssignTuplePlaces' root
   assigns, except one case left admitted: an immutable assigned in the
   constructor.
   TOP-LEVEL: assign_tuple_other_shapes, tuple_places_targets_ready,
   body_assign_tuple_places; immutable_deploy_tuple_assign (RESIDUAL). *)
Theory bodyAssignTupleOther
Ancestors
  stmtSimAssignTuplePlaces targetPlaceSimCases targetPlaceSim bodySimExprCases
  bodyExprPreFacts bodySim
  exprSimAggregateLayout exprSimHypsDefs bodyStorageMetadata
  supportedStmts supportedDecls vyperTypeSystem vyperTypeInvariants vyperTypeEnv
  list finite_map vyperTypeValues exprSimHyps valueEncoding compileEnv vyperState supportedExprForms supportedTargets
  supportedStmtTraverse supportedExprTraverse gasContext vyperTypeCallGraph
  vyperTypeCallStackSoundness allocLimits targetPlaceLive

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
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
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

Theorem tuple_places_typing:
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' ==>
  ?tys tvs. expr_type e = TupleT tys /\ gs <> [] /\
    LIST_REL (\g ty. well_typed_atarget env g ty) gs tys /\
    assignable_type (get_tenv cx) (TupleT tys) /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs)
Proof
  rpt strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
      AllCaseEqs()] >>
  rename1 `expr_type e = TupleT tys` >>
  `?tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tv` by
    metis_tac[assignable_type_well_formed, well_formed_type_def,
              optionTheory.IS_SOME_EXISTS] >>
  drule evaluate_type_TupleT_cases >> strip_tac >>
  qexists_tac `tvs` >> simp[] >>
  Cases_on `gs` >> gvs[assignable_type_def] >>
  fs[ETA_AX]
QED

Theorem tuple_places_member_size[local]:
  !tvs i. i < LENGTH tvs ==>
    type_memory_size (EL i tvs) <= type_memory_size (TupleTV tvs)
Proof
  Induct >> simp[type_memory_size_def] >>
  Cases_on `i` >> simp[type_memory_size_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[type_memory_size_def]
QED

Theorem tuple_places_component_bound:
  expr_body_pre cenv cx env e es /\ expr_type e = TupleT tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) ==>
  !i. i < LENGTH tys /\ ~is_word_type (EL i tys) ==>
    type_memory_size (EL i tvs) + 64 < dimword (:256)
Proof
  rpt strip_tac >>
  `~is_word_type (expr_type e)` by simp[is_word_type_def] >>
  `type_memory_size (TupleTV tvs) < 2 ** 64` by
    (drule expr_body_pre_copy_ok >>
     disch_then (qspec_then `TupleTV tvs` mp_tac) >> simp[]) >>
  drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  `LENGTH tys = LENGTH tvs` by metis_tac[LIST_REL_LENGTH] >>
  `type_memory_size (EL i tvs) <= type_memory_size (TupleTV tvs)` by
    (irule tuple_places_member_size >> simp[]) >>
  simp[wordsTheory.dimword_def] >> decide_tac
QED

Theorem tuple_places_storage_decl[local]:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >>
  rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem tuple_places_hashmap_decl[local]:
  !ts src id vis tr kt vt slot.
    supported_hashmap_decl ts (src,id) = SOME (vis,tr,kt,vt,slot) ==>
    src = NONE /\ find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[supported_hashmap_decl_def] >> Cases >>
  rw[supported_hashmap_decl_def, find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem tuple_places_scalar_decl[local]:
  supported_scalar_target tops (src,id) ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE
Proof
  simp[supported_scalar_target_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `supported_variable_decl _ _ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> simp[] >>
  Cases_on `decl1` >> simp[] >>
  Cases_on `decl3` >> simp[] >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> simp[] >>
  metis_tac[tuple_places_storage_decl]
QED

Theorem tuple_places_array_decl[local]:
  supported_storage_array tops (src,id) ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE
Proof
  simp[supported_storage_array_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `supported_variable_decl _ _ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> simp[] >>
  Cases_on `decl1` >> simp[] >>
  Cases_on `decl2` >> simp[] >>
  Cases_on `decl3` >> simp[] >> strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> simp[] >>
  metis_tac[tuple_places_storage_decl]
QED

Theorem tuple_places_fields_decl[local]:
  supported_storage_fields tops (src,id) = SOME fields ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE
Proof
  simp[supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `supported_variable_decl _ _ = SOME decl` >> PairCases_on `decl` >>
  Cases_on `decl0` >> simp[] >>
  Cases_on `decl1` >> simp[] >>
  Cases_on `decl2` >> simp[] >>
  Cases_on `decl3` >> simp[] >>
  strip_tac >>
  drule supported_variable_decl_mem >> strip_tac >> simp[] >>
  metis_tac[tuple_places_storage_decl]
QED

Theorem tuple_places_storage_root[local]:
  get_module_code cx NONE = SOME tops /\
  (supported_scalar_target tops nsid \/ supported_subscript_base tops nsid \/
   supported_storage_field_write tops nsid fld) ==>
  ~immutable_root cx (TopLevelNameTarget nsid)
Proof
  PairCases_on `nsid` >>
  rw[immutable_root_def, target_root_def] >>
  imp_res_tac tuple_places_scalar_decl >>
  gvs[supported_subscript_base_def, supported_storage_field_write_def] >>
  imp_res_tac tuple_places_array_decl >>
  gvs[]
  >~ [`supported_hashmap_decl tops (src,id)`]
  >- (Cases_on `supported_hashmap_decl tops (src,id)` >> gvs[] >>
      rename1 `supported_hashmap_decl _ _ = SOME decl` >>
      PairCases_on `decl` >>
      drule tuple_places_hashmap_decl >> strip_tac >> gvs[])
  >~ [`supported_storage_fields tops (src,id)`]
  >- (Cases_on `supported_storage_fields tops (src,id)` >> gvs[] >>
      drule tuple_places_fields_decl >> strip_tac >> gvs[])
QED

Theorem tuple_places_member:
  get_module_code cx NONE = SOME tops /\
  expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  ~EXISTS (\g. ?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
    cx.in_deploy /\ IS_SOME (supported_immutable_type tops nsid)) gs /\
  MEM g gs ==>
  ?bt ty. g = BaseTarget bt /\ supported_target tops bindings bt /\
    EVERY (supported_expr tops) (target_indices bt) /\ ~immutable_root cx bt /\
    well_typed_atarget env g ty
Proof
  rpt strip_tac >>
  drule_all tuple_places_typing >> strip_tac >>
  `?ty. well_typed_atarget env g ty` by
    (drule_all LIST_REL_MEM_IMP >> simp[] >> metis_tac[]) >>
  `?bt. g = BaseTarget bt /\ supported_target tops bindings bt` by
    (gvs[supported_stmt_def, supported_assignment_def, EVERY_MEM] >>
     qpat_x_assum `!g. MEM g gs ==> (case g of BaseTarget bt => _ | TupleTarget ts => _)`
       (qspec_then `g` mp_tac) >>
     Cases_on `g` >> simp[]) >>
  gvs[EVERY_MEM] >> qexists_tac `ty` >> simp[] >>
  Cases_on `bt` >> gvs[supported_target_def, target_indices_def]
  >~ [`NameTarget id`]
  >- simp[immutable_root_def, target_root_def]
  >~ [`supported_scalar_target tops nsid`]
  >- (irule tuple_places_storage_root >> goal_assum drule >> simp[])
  >~ [`TopLevelNameTarget nsid`]
  >- (`~cx.in_deploy` by metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE] >>
      `bare_globals_complete env.bare_globals cx /\
       bare_global_assignable_complete env.bare_global_assignable cx` by
        gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
      gvs[optionTheory.IS_SOME_EXISTS, supported_immutable_type_def,
          well_typed_atarget_def, well_typed_target_def, AllCaseEqs()] >>
      PairCases_on `nsid` >> drule supported_variable_decl_mem >> strip_tac >>
      gvs[bare_globals_complete_def, bare_global_assignable_complete_def] >>
      first_x_assum (drule_then drule) >> strip_tac >>
      qpat_x_assum `type_place_target _ _ = _` mp_tac >>
      simp[Once well_typed_expr_def])
  >~ [`SubscriptTarget t key`]
  >- (Cases_on `t` >> gvs[target_indices_def, target_root_def] >>
      `~immutable_root cx (TopLevelNameTarget p)` by
        (irule tuple_places_storage_root >> goal_assum drule >> simp[]) >>
      gvs[immutable_root_def, target_root_def])
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[target_indices_def, target_root_def] >>
      `~immutable_root cx (TopLevelNameTarget p)` by
        (irule tuple_places_storage_root >> goal_assum drule >>
         qexists_tac `fld` >> simp[]) >>
      gvs[immutable_root_def, target_root_def])
QED

Theorem tuple_places_member_occurs[local]:
  !gs. MEM (BaseTarget bt) gs /\ supported_target_exists p bt ==>
    supported_stmt_expr_exists p (Assign (TupleTarget gs) e)
Proof
  Induct >> gvs[supported_stmt_expr_exists_def,
    supported_assignment_exists_def] >> rpt strip_tac >>
  gvs[supported_assignment_exists_def] >> metis_tac[]
QED

Theorem tuple_places_member_alloc[local]:
  !gs. MEM (BaseTarget bt) gs /\ alloc_limits_assignments cenv gs ==>
    alloc_limits_target cenv bt
Proof
  Induct >> rw[alloc_limits_assignment_def] >> gvs[alloc_limits_assignment_def]
QED

Theorem tuple_places_member_calls[local]:
  !gs. MEM (BaseTarget bt) gs /\
    call_evaluation_safe cx (int_calls_atargets gs) ==>
    call_evaluation_safe cx (int_calls_target bt)
Proof
  Induct >> simp[int_calls_atarget_def] >> rpt strip_tac >>
  metis_tac[int_calls_atarget_def, call_evaluation_safe_append_left,
    call_evaluation_safe_append_right]
QED

Theorem tuple_places_member_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  MEM (BaseTarget bt) gs ==>
  target_indices_pre cenv cx env bt /\
  call_evaluation_safe cx (int_calls_target bt)
Proof
  rpt strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule tuple_places_member_calls >> goal_assum drule >>
     gvs[int_calls_stmt_def, int_calls_atarget_def] >>
     metis_tac[call_evaluation_safe_append_left]) >>
  simp[] >>
  `supported_target tops bindings bt` by
    (gvs[supported_stmt_def, supported_assignment_def, EVERY_MEM] >>
     first_x_assum drule >> simp[]) >>
  `?ty. well_typed_atarget env (BaseTarget bt) ty` by
    (gvs[type_stmt_def, atarget_accepts_def, well_typed_atarget_def,
       AllCaseEqs()] >> drule_all LIST_REL_MEM_IMP >>
     metis_tac[well_typed_atarget_def]) >>
  Cases_on `bt` >> gvs[supported_target_def, target_indices_pre_def]
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[target_indices_pre_def]) >>
  rename1 `target_indices_pre cenv cx env root` >>
  Cases_on `root` >> gvs[target_indices_pre_def] >>
  rename1 `SubscriptTarget (TopLevelNameTarget nsid) key` >>
  `alloc_limits_target cenv (SubscriptTarget (TopLevelNameTarget nsid) key)` by
    (irule tuple_places_member_alloc >> goal_assum drule >>
     gvs[stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_assignment_def]) >>
  gvs[Once alloc_limits_expr_def] >> rpt strip_tac >>
  `well_typed_expr env key` by
    gvs[well_typed_atarget_def, well_typed_target_def,
        type_place_target_SubscriptTarget] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> gvs[body_inv_def]) >>
  `!p. supported_expr_exists p key ==>
     supported_stmt_expr_exists p (Assign (TupleTarget gs) e)` by
    (rpt strip_tac >> irule tuple_places_member_occurs >>
     goal_assum drule >> simp[supported_expr_exists_def]) >>
  irule stmt_expr_body_pre >> simp[] >>
  conj_tac >- gvs[body_inv_def] >>
  conj_tac >- (gvs[stmt_exprs_ok_flat] >> metis_tac[]) >>
  conj_tac >- (strip_tac >> qexists_tac `tops` >> gvs[body_inv_def]) >>
  qexists_tac `[]` >> gvs[int_calls_expr_def]
QED

(* Every element of a supported tuple assignment outside a constructor's
   immutables is a place compile_assign_tuple_places_stmt_frag takes: its
   indices are supported (an internal call among them included), and its
   static facts hold. *)
Theorem tuple_places_targets_ready:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  ~EXISTS (\g. ?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
    cx.in_deploy /\ IS_SOME (supported_immutable_type tops nsid)) gs ==>
  EVERY (\g. ?bt. g = BaseTarget bt /\
                  EVERY (supported_expr tops) (target_indices bt) /\
                  (body_base_target_ok cx bt ==>
                   target_case F ctx func cenv cx bt) /\
                  ~immutable_root cx bt /\ target_indices_pre cenv cx env bt /\
                  call_evaluation_safe cx (int_calls_target bt)) gs
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  `get_module_code cx NONE = SOME tops` by gvs[body_inv_def] >>
  drule_all tuple_places_member >> strip_tac >> gvs[] >>
  drule_all tuple_places_member_pre >> strip_tac >> fs[EVERY_MEM] >>
  metis_tac[target_case_all, bodyPopNestedTargetFragTheory.body_target_idx_case]
QED

Theorem tuple_other_arg_types_fit_refl[local]:
  !ts. arg_types_fit ts ts
Proof
  gen_tac >> mp_tac (Q.SPEC `TupleT ts` exprSimHypsTheory.ifexp_arg_type_fits_refl) >>
  simp[arg_type_fits_def]
QED

(* body_assign_tuple_other for an RHS lowered at its own type: the
   residual case, and otherwise every element is a place outside an
   immutable, which compile_assign_tuple_places_stmt_frag
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
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
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
  rpt strip_tac >>
  Cases_on `EXISTS (\g. ?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
    cx.in_deploy /\ IS_SOME (supported_immutable_type tops nsid)) gs`
  >- (irule immutable_deploy_tuple_assign >> metis_tac[]) >>
  drule_all tuple_places_typing >> strip_tac >>
  `get_module_code cx NONE = SOME tops /\
   acyclic_struct_metadata cenv.ce_struct_fields` by gvs[body_inv_def] >>
  `expr_sim ctx func cenv cx (TupleT tys) e es` by
    (drule_all body_expr_ok_case >>
     disch_then (qspec_then `func` strip_assume_tac) >>
     gvs[expr_sim_case_def] >> metis_tac[]) >>
  drule_all tuple_places_targets_ready >> strip_tac >>
  irule compile_assign_tuple_places_stmt_frag >>
  simp[tuple_other_arg_types_fit_refl] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`env`, `tops`] >> simp[] >>
  metis_tac[tuple_places_component_bound]
QED
