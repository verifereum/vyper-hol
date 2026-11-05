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
  stmtSimAssignPlace

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
    target_case F ctx func cenv cx bt /\ target_env_ok cenv cx /\
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
  cheat
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
  cheat
QED
