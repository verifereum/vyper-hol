(*
 * The residual augmented assignment targets of bodySimStmtCases'
 * body_augassign_other: what supported_stmt admits for AugAssign beyond a
 * local, a full-word storage or transient variable, a field of a local, and
 * a supported field of a storage or transient struct.
 *
 * TOP-LEVEL:
 *   supported_aug_toplevel_decl — a supported augmented top-level target
 *                       is a word variable of tops in storage or transient
 *                       storage (any word width, not only full words)
 *   body_augassign_other_leaf — body_augassign_other, with the abi-decode
 *                       premise of body_stmt_ok
 *   supported_aug_attr_toplevel_field — a supported augmented field of a
 *                       top-level variable is a supported storage field
 *)
Theory bodyAugAssignOther
Ancestors
  supportedStmts supportedTargets supportedExprForms supportedDecls
  supportedTypes bodyStorageMetadata compileEnv vyperAST list alist
  bodySim stmtSimDefs exprSimHypsDefs targetPlaceSim targetPlaceSimCases
  vyperTypeEnv vyperTypeInvariants vyperTypeSystem vyperInterpreter
  vyperContext stmtSimAugAssignStorage stmtSimAugAssignPlace
  stmtSimAugAssignPlaceMemory stmtSimAugAssignPlaceStorage bodyAugPlaceTarget
  bodyExprPreFacts bodySimExprCases
  supportedStmtTraverse vyperTypeCallGraph vyperState exprSimTopLevelProps

Theorem supported_word_type_is_word:
  !ty. supported_word_type ty ==> is_word_type ty
Proof
  Cases >> simp[supported_word_type_def, is_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, is_word_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, is_word_type_def]
QED

Theorem supported_aug_toplevel_decl:
  !tops bindings src id.
    supported_aug_target tops bindings (TopLevelNameTarget (src, id)) ==>
    src = NONE /\
    ?vis mut ty slot. MEM (VariableDecl vis mut id ty slot) tops /\
                      (mut = Storage \/ mut = Transient) /\ is_word_type ty
Proof
  rpt gen_tac >>
  simp[supported_aug_target_def, supported_target_info_def,
       supported_place_root_def] >>
  Cases_on `supported_hashmap_decl tops (src, id)`
  >- (Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
      rename1 `SOME x` >> PairCases_on `x` >>
      drule supported_variable_decl_mem >> strip_tac >>
      Cases_on `x3` >> Cases_on `x0` >> Cases_on `x1` >> simp[] >>
      rw[] >> gvs[] >> first_assum (irule_at Any) >>
      simp[supported_word_type_is_word]) >>
  rename1 `SOME y` >> PairCases_on `y` >> rw[]
QED

Theorem supported_aug_attr_toplevel_field:
  !tops bindings nsid fld.
    supported_aug_target tops bindings
      (AttributeTarget (TopLevelNameTarget nsid) fld) ==>
    supported_storage_field_write tops nsid fld
Proof
  rpt gen_tac >>
  simp[supported_aug_target_def, supported_target_info_def,
       supported_place_root_def, supported_storage_field_write_def,
       supported_storage_fields_def] >>
  Cases_on `supported_hashmap_decl tops nsid`
  >- (Cases_on `supported_variable_decl tops nsid` >> simp[] >>
      rename1 `SOME x` >> PairCases_on `x` >>
      Cases_on `x3` >> Cases_on `x0` >> Cases_on `x1` >> simp[] >>
      rw[] >> Cases_on `x2` >> gvs[] >>
      Cases_on `supported_struct_fields tops p` >> gvs[] >>
      Cases_on `ALOOKUP x' fld` >> gvs[MEM_MAP, PULL_EXISTS] >>
      drule ALOOKUP_MEM >> strip_tac >> first_assum (irule_at Any) >> simp[]) >>
  rename1 `SOME y` >> PairCases_on `y` >> rw[]
QED

(* An immutable at runtime has no assignable type: bare_global_assignable is
   empty outside the constructor and the immutable is a bare global. *)
Theorem augassign_immutable_runtime_untyped:
  !env cx tops src id ity.
    env_context_consistent env cx /\ ~cx.in_deploy /\
    get_module_code cx NONE = SOME tops /\
    supported_immutable_type tops (src,id) = SOME ity ==>
    type_place_target env (TopLevelNameTarget (src,id)) = NONE
Proof
  rpt strip_tac >>
  gvs[supported_immutable_type_def, AllCaseEqs()] >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >> simp[] >>
  gvs[type_place_target_TopLevelNameTarget, env_context_consistent_def,
      bare_global_assignable_complete_def, bare_globals_complete_def] >>
  qpat_x_assum `!src ts vis mut id ty init. _`
    (qspecl_then [`NONE`,`tops`,`Private`,`Immutable`,`id`,`ity`,`NONE`]
       mp_tac) >> simp[]
QED

(* ADMITTED: x op= e on an immutable in the constructor, until
   immutable_alloca_sep and body_inv relate the constructor's immutables
   buffer to the source's immutables. *)
Theorem immutable_deploy_augassign_case:
  !ctx func cx lctx RetQ cenv ret_ty env env' tops nsid ty bop e es ity.
    body_inv tops ctx cenv cx /\ cx.in_deploy /\
    supported_immutable_type tops nsid = SOME ity /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e) =
      SOME env' /\
    ((?s p s1 s2 cur s3 s4 ptv s5.
        eval_target_place cx (TopLevelNameTarget nsid) s = (INL p,s1) /\
        read_place cx p s2 = (INL cur,s3) /\
        place_type_value cx p s4 = (INL ptv,s5)) ==>
     expr_sim_case F ctx func cenv cx e) /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget nsid) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget nsid) bop e)) es
Proof
  cheat
QED

(* ADMITTED: x op= e at a storage place whose indices have effects, as
   targetPlaceSimCases' pop_nested_storage_effectful_sim. *)
Theorem augassign_place_effectful_index_case:
  !ctx func cx lctx RetQ cenv ret_ty env env' tops bindings ty bt bop e es.
    (!id. target_root bt <> NameTarget id) /\ ~supported_target_pure tops bt /\
    ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty bt bop e) /\
    type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
    target_case F ctx func cenv cx bt /\
    ~immutable_root cx bt /\ target_indices_pre cenv cx env bt /\
    ((?s p s1 s2 cur s3 s4 ptv s5.
        eval_target_place cx bt s = (INL p,s1) /\
        read_place cx p s2 = (INL cur,s3) /\
        place_type_value cx p s4 = (INL ptv,s5)) ==>
     expr_sim_case F ctx func cenv cx e) /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty bt bop e))
      (eval_stmt cx (AugAssign ty bt bop e)) es
Proof
  cheat
QED

Theorem aug_storage_decl_some[local]:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem aug_assignable_find_NONE[local]:
  !env cx st src id ty.
    env_consistent env cx st /\
    FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==>
    ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem augassign_rhs_pre[local]:
  body_inv tops ctx cenv cx /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  drule supported_expr_body_calls >> strip_tac >>
  gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
      int_calls_stmt_def, AllCaseEqs()] >>
  irule stmt_expr_body_pre >>
  fs[body_inv_def, gasContextTheory.cx_tops_def] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right,
            APPEND_NIL]
QED

Theorem augassign_rhs_case[local]:
  body_inv tops ctx cenv cx /\
  (!s p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx t s = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ok cx e) ==>
  ((?s p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx t s = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5)) ==>
   expr_sim_case F ctx func cenv cx e)
Proof
  metis_tac[body_expr_ok_case]
QED

Theorem augassign_toplevel_metadata[local]:
  body_inv tops ctx cenv cx /\
  supported_aug_target tops bindings (TopLevelNameTarget (src,id)) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) =
    SOME env' ==>
  src = NONE /\
  ?tr id_str slot tvt.
    get_module_code cx src = SOME tops /\
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\
    well_formed_type env.type_defs ty /\
    cenv.ce_hashmap_info (src,id) = NONE /\
    cenv.ce_module_var_type (src,id) = SOME ty /\ is_word_type ty /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn
Proof
  rpt strip_tac >>
  drule supported_aug_toplevel_decl >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `vis` (qx_choose_then `mut`
      (qx_choose_then `dty` (qx_choose_then `init` assume_tac))))) >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[aug_storage_decl_some] >>
  gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `type_place_target env (TopLevelNameTarget (NONE,id)) = SOME (Type ty) /\
   assignable_type env.type_defs ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
  `FLOOKUP env.bare_global_assignable (NONE,id) = NONE` by
    (Cases_on `FLOOKUP env.bare_global_assignable (NONE,id)` >> simp[] >>
     drule_all aug_assignable_find_NONE >> strip_tac >> gvs[]) >>
  gvs[type_place_target_TopLevelNameTarget] >>
  drule_all env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `dty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  metis_tac[assignable_type_well_formed]
QED

Theorem augassign_target_case[local]:
  body_base_target_ok cx t /\ body_inv tops ctx cenv cx ==>
  target_case F ctx func cenv cx t
Proof
  metis_tac[aug_place_body_target_idx, target_case_all]
QED

Theorem augassign_target_not_immutable[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  ((?b fld. t = AttributeTarget b fld) \/ (?b k. t = SubscriptTarget b k)) ==>
  ~immutable_root cx t
Proof
  metis_tac[aug_place_supported_stmt_target_info,
            aug_place_supported_root_not_immutable]
QED

Theorem augassign_target_pre[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  ((?b fld. t = AttributeTarget b fld) \/ (?b k. t = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty t bop e) /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) ==>
  target_indices_pre cenv cx env t
Proof
  rpt strip_tac >>
  `?pt. supported_target_info tops bindings t = SOME pt` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  irule aug_place_target_indices_pre >>
  gvs[type_stmt_def, well_typed_target_def, stmt_exprs_ok_def,
      supported_stmt_expr_exists_def, int_calls_stmt_def, AllCaseEqs()] >>
  fs[body_inv_def] >>
  metis_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left,
            optionTheory.IS_SOME_EXISTS]
QED

Theorem augassign_toplevel_success[local]:
  body_inv tops ctx cenv cx /\
  supported_aug_target tops bindings (TopLevelNameTarget (src,id)) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) =
    SOME env' ==>
  ?s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx (TopLevelNameTarget (src,id)) s = (INL p,s1) /\
    read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5)
Proof
  rpt strip_tac >>
  drule_all augassign_toplevel_metadata >> strip_tac >>
  `contract_storage_well_formed cx es` by fs[expr_sim_inv_def] >>
  drule_all toplevel_storage_read_decodes >> strip_tac >>
  drule_all eval_target_place_toplevel >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  metis_tac[read_place_def]
QED

(* x op= e on a word storage or transient variable of any width:
   stmtSimAugAssignStorage's compile_augassign_toplevel_case. *)
Theorem body_augassign_toplevel_aug:
  !cx ty src id bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\
    body_inv tops ctx cenv cx /\
    supported_aug_target tops bindings (TopLevelNameTarget (src, id)) /\
    supported_expr tops e /\ expr_sim_inv cenv cx env es /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty (TopLevelNameTarget (src, id)) bop e) ==>
       occurs_abi_decode_target target tops) /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) =
      SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx
      (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  rpt strip_tac >>
  drule_all augassign_rhs_pre >> strip_tac >>
  drule_all augassign_toplevel_success >> strip_tac >>
  `body_expr_ok cx e` by metis_tac[] >>
  `expr_sim_case F ctx func cenv cx e` by
    metis_tac[body_expr_ok_case] >>
  drule_all augassign_toplevel_metadata >> strip_tac >>
  irule compile_augassign_toplevel_case >>
  simp[] >> metis_tac[]
QED

(* The residual augmented assignments of bodySimStmtCases'
   body_augassign_other.  By the target: a word storage or transient
   variable of any width (body_augassign_toplevel_aug); an immutable, which
   has no assignable type at runtime (augassign_immutable_runtime_untyped)
   and is immutable_deploy_augassign_case in the constructor; a field or
   element of a local (compile_augassign_place_memory_case); and a field or
   element of a storage or transient variable, with pure indices
   (compile_augassign_place_storage_case) or not
   (augassign_place_effectful_index_case). *)
Theorem body_augassign_other_leaf:
  !cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ok cx e) /\ body_base_target_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty t bop e) ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    ~(?id. t = NameTarget id) /\
    ~(?nsid. t = TopLevelNameTarget nsid /\
             supported_scalar_target tops nsid) /\
    ~(?id fld. t = AttributeTarget (NameTarget id) fld) /\
    ~(?nsid fld. t = AttributeTarget (TopLevelNameTarget nsid) fld /\
                 supported_storage_field_write tops nsid fld) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by fs[supported_stmt_def] >>
  drule_all augassign_rhs_pre >> strip_tac >>
  `((?s p s1 s2 cur s3 s4 ptv s5.
      eval_target_place cx t s = (INL p,s1) /\
      read_place cx p s2 = (INL cur,s3) /\
      place_type_value cx p s4 = (INL ptv,s5)) ==>
    expr_sim_case F ctx func cenv cx e)` by metis_tac[augassign_rhs_case] >>
  `target_case F ctx func cenv cx t` by metis_tac[augassign_target_case] >>
  Cases_on `t`
  >- gvs[]
  >- (rename1 `TopLevelNameTarget nsid` >> PairCases_on `nsid` >>
      Cases_on `supported_aug_target tops bindings
        (TopLevelNameTarget (nsid0,nsid1))`
      >- metis_tac[body_augassign_toplevel_aug] >>
      `?ity. supported_immutable_type tops (nsid0,nsid1) = SOME ity` by
        gvs[supported_stmt_def, supported_target_def, optionTheory.IS_SOME_EXISTS] >>
      Cases_on `cx.in_deploy`
      >- (irule immutable_deploy_augassign_case >> metis_tac[]) >>
      `env_context_consistent env cx /\ get_module_code cx NONE = SOME tops` by
        fs[expr_sim_inv_def, env_consistent_def, body_inv_def] >>
      drule_all augassign_immutable_runtime_untyped >> strip_tac >>
      gvs[type_stmt_def, well_typed_target_def]) >>
  (qmatch_goalsub_abbrev_tac `AugAssign ty bt bop e` >>
  `((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k))` by
    simp[Abbr `bt`] >>
  (`~immutable_root cx bt` by metis_tac[augassign_target_not_immutable] >>
  `target_indices_pre cenv cx env bt` by metis_tac[augassign_target_pre] >>
  Cases_on `?id. target_root bt = NameTarget id`
  >- (irule compile_augassign_place_memory_case >> metis_tac[]) >>
  Cases_on `supported_target_pure tops bt`
  >- (irule compile_augassign_place_storage_case >> metis_tac[]) >>
  irule augassign_place_effectful_index_case >> simp[] >> metis_tac[]))
QED
