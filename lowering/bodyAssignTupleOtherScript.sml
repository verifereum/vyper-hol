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
  stmtSimAssignTuplePlaces targetPlaceSimCases targetPlaceSim bodySimExprCases
  bodyExprPreFacts bodySim
  exprSimAggregateLayout exprSimHypsDefs bodyStorageMetadata
  supportedStmts supportedDecls vyperTypeSystem vyperTypeInvariants vyperTypeEnv
  list finite_map vyperTypeValues exprSimHyps valueEncoding compileEnv vyperState supportedExprForms supportedTargets
  supportedStmtTraverse supportedExprTraverse gasContext vyperTypeCallGraph

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
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (TupleTarget gs) e) ==>
       occurs_abi_decode_target target tops) /\
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

Theorem tuple_places_typing[local]:
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

Theorem tuple_places_component_bound[local]:
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

Theorem tuple_places_member[local]:
  get_module_code cx NONE = SOME tops /\
  expr_sim_inv cenv cx env es /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  ~EXISTS (\g. ?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
    cx.in_deploy /\ IS_SOME (supported_immutable_type tops nsid)) gs /\
  ~EXISTS (\g. ?nsid key.
    g = BaseTarget (SubscriptTarget (TopLevelNameTarget nsid) key) /\
    ~supported_pure_expr tops key) gs /\ MEM g gs ==>
  ?bt ty. g = BaseTarget bt /\ supported_target tops bindings bt /\
    supported_target_pure tops bt /\ ~immutable_root cx bt /\
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
  Cases_on `bt` >> gvs[supported_target_def, supported_target_pure_def]
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
  >- (Cases_on `t` >> gvs[supported_target_pure_def, target_root_def] >>
      conj_tac >- metis_tac[] >>
      `~immutable_root cx (TopLevelNameTarget p)` by
        (irule tuple_places_storage_root >> goal_assum drule >> simp[]) >>
      gvs[immutable_root_def, target_root_def])
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[supported_target_pure_def, target_root_def] >>
      `~immutable_root cx (TopLevelNameTarget p)` by
        (irule tuple_places_storage_root >> goal_assum drule >>
         qexists_tac `fld` >> simp[]) >>
      gvs[immutable_root_def, target_root_def])
QED

(* An expression with no internal call is body_expr_ok: a subscript by
   body_subscript_case on its parts, anything else by body_expr_ok_intro,
   whose internal-call premise is then vacuous. *)
Theorem tuple_places_no_calls_body_expr_ok[local]:
  !e. int_calls_expr e = [] ==> body_expr_ok cx e
Proof
  measureInduct_on `expr_size e` >> rpt strip_tac >>
  Cases_on `?ty e1 e2. e = Subscript ty e1 e2`
  >- (gvs[] >> irule body_subscript_case >>
      gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
      conj_tac >> rpt strip_tac >> qpat_assum `!y. _` irule >>
      gvs[vyperASTTheory.expr_size_def]) >>
  irule body_expr_ok_intro >> gvs[] >> metis_tac[]
QED

Theorem tuple_places_target_case[local]:
  body_inv tops ctx cenv cx /\ supported_target tops bindings bt /\
  supported_target_pure tops bt ==>
  target_case F ctx func cenv cx bt
Proof
  rpt strip_tac >> irule target_case_all >>
  Cases_on `bt` >> gvs[supported_target_def, target_idx_case_def]
  >~ [`SubscriptTarget t key`]
  >- (Cases_on `t` >> gvs[target_idx_case_def, supported_target_pure_def] >>
      rpt strip_tac >>
      `int_calls_expr key = []` by metis_tac[supported_pure_int_calls] >>
      `body_expr_ok cx key` by metis_tac[tuple_places_no_calls_body_expr_ok] >>
      metis_tac[body_expr_ok_case])
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[target_idx_case_def])
QED

Theorem tuple_places_key_occurs[local]:
  !gs. MEM (BaseTarget (SubscriptTarget (TopLevelNameTarget nsid) key)) gs /\
    supported_expr_exists p key ==>
    supported_stmt_expr_exists p (Assign (TupleTarget gs) e)
Proof
  Induct >> gvs[supported_stmt_expr_exists_def,
    supported_assignment_exists_def, supported_expr_exists_def] >>
  rpt strip_tac >> gvs[supported_assignment_exists_def,
                       supported_expr_exists_def] >> metis_tac[]
QED

Theorem tuple_places_key_pre[local]:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  well_typed_expr env key /\ supported_expr tops key /\
  call_evaluation_safe cx calls /\ supported_pure_expr tops key /\
  MEM (BaseTarget (SubscriptTarget (TopLevelNameTarget nsid) key)) gs /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) ==>
  expr_body_pre cenv cx env key es
Proof
  rpt strip_tac >>
  `int_calls_expr key = []` by metis_tac[supported_pure_int_calls] >>
  `~expr_has_evm_run key /\ ~is_extcode key` by
    metis_tac[supported_expr_body_calls] >>
  `~supported_expr_exists
    (\e. ~is_extcode e /\
          ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) key` by
    (gvs[stmt_exprs_ok_def] >> metis_tac[tuple_places_key_occurs]) >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> gvs[body_inv_def]) >>
  irule stmt_expr_body_pre >> simp[] >>
  conj_tac >- gvs[body_inv_def] >>
  conj_tac >- metis_tac[tuple_places_key_occurs] >>
  conj_tac >- metis_tac[supported_expr_no_call_operand_effects] >>
  qexists_tac `calls` >> simp[]
QED

Theorem tuple_places_indices_pre[local]:
  body_inv tops ctx cenv cx /\ supported_target tops bindings bt /\
  supported_target_pure tops bt /\ well_typed_atarget env (BaseTarget bt) ty /\
  MEM (BaseTarget bt) gs /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx calls /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) ==>
  target_indices_pre cenv cx env bt
Proof
  rpt strip_tac >>
  Cases_on `bt` >> gvs[supported_target_def, target_indices_pre_def]
  >~ [`SubscriptTarget t key`]
  >- (Cases_on `t` >> gvs[target_indices_pre_def, supported_target_pure_def] >>
      rpt strip_tac >>
      `well_typed_expr env key` by
        gvs[well_typed_atarget_def, well_typed_target_def,
            type_place_target_SubscriptTarget] >>
      metis_tac[tuple_places_key_pre])
  >~ [`AttributeTarget t fld`]
  >- (Cases_on `t` >> gvs[target_indices_pre_def])
QED

Theorem tuple_other_arg_type_fits_refl[local]:
  !t. arg_type_fits t t
Proof
  Induct >> simp[arg_type_fits_def]
  >- (Cases >> simp[arg_type_fits_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >> simp[arg_type_fits_def])
  >- (Induct_on `l` >> simp[arg_type_fits_def]) >>
  Cases >> simp[arg_type_fits_def]
QED

Theorem tuple_other_arg_types_fit_refl[local]:
  !ts. arg_types_fit ts ts
Proof
  gen_tac >> mp_tac (Q.SPEC `TupleT ts` tuple_other_arg_type_fits_refl) >>
  simp[arg_type_fits_def]
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
  Cases_on `EXISTS (\g. ?nsid key.
    g = BaseTarget (SubscriptTarget (TopLevelNameTarget nsid) key) /\
    ~supported_pure_expr tops key) gs`
  >- (irule tuple_assign_effectful_index >> metis_tac[]) >>
  drule_all tuple_places_typing >> strip_tac >>
  `get_module_code cx NONE = SOME tops /\
   acyclic_struct_metadata cenv.ce_struct_fields` by gvs[body_inv_def] >>
  `expr_sim ctx func cenv cx (TupleT tys) e es` by
    (drule_all body_expr_ok_case >>
     disch_then (qspec_then `func` strip_assume_tac) >>
     gvs[expr_sim_case_def] >> metis_tac[]) >>
  `EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target_pure tops bt /\
    target_case F ctx func cenv cx bt /\ ~immutable_root cx bt /\
    target_indices_pre cenv cx env bt) gs` by
    (rw[EVERY_MEM] >>
     drule_all tuple_places_member >> strip_tac >> gvs[] >>
     conj_tac
     >- metis_tac[tuple_places_target_case] >>
     metis_tac[tuple_places_indices_pre]) >>
  irule compile_assign_tuple_places_stmt_frag >>
  simp[tuple_other_arg_types_fit_refl] >>
  qexistsl_tac [`env`, `tops`] >> simp[] >>
  metis_tac[tuple_places_component_bound]
QED
