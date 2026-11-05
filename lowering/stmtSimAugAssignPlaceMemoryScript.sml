(*
 * Augmented assignment to a field or an element inside a local (#637): the
 * place is in memory (aug_place_name_root_memory).  The current word is
 * loaded by MLOAD at the place's pointer, combined with the right-hand
 * side, and stored back by MSTORE.
 *
 * TOP-LEVEL:
 *   compile_augassign_place_memory_case
 *)
Theory stmtSimAugAssignPlaceMemory
Ancestors
  valueEncodingProps
  exprSimSource bodyExprPreFacts exprSimTopLevelProps stmtSimBreak stmtSimContinue stmtSimExpr stmtSimSeqEnv stmtSimPass stmtSimProps exprSimHypsDefs stmtSimZero stmtSimDefs loweringPosts bodyAppendStorageFacts bodyAppendStorageAdapter
  vyperStorageLayoutSafety vyperLookupStorage
  list finite_map bodySim allocLimits allocLimitsProps  exprSimHyps exprLoweringProps
  stmtSimIf stmtLoweringMono stmtLowering compileEnv fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage stmtSimReasonCode supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  exprReasonOperand
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple
  vyperTypeEnvPreservation bodySimExprCases bodyStoragePreservation
  vyperCallOutcomeStorage vyperTypeStoragePreservation
  stmtSimAssignStorage supportedDecls vyperTypeContractStaticMaps
  vyperTypeContract compileVyper supportedTypes stmtSimAssignAttr
  stmtSimAssignStorageCopy
  stmtSimAugAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignStorage
  stmtSimAugAssignAttrStorage stmtSimAssignMem stmtSimAssignTupleMem
  stmtSimAssignTupleTargets
  memoryLocalRhsProps stmtPoppedKeys exprOpenMain bodyStorageMetadata
  vyperPureExpr targetPlaceSim targetPlaceSimCases exprSimDefs
  placeStore supportedTargets exprSimProps exprSimSource loweringPosts
  bodyAugPlaceTarget
  stmtSimAugAssignPlace bodySimAugPlaceLoad bodySimAugPlaceLive
Libs
  monadsyntax

Theorem aug_place_rhs_ready:
  (!s0 p s1 s2 cur s3 s4 ptv s5.
     eval_target_place cx t s0 = (INL p,s1) /\
     read_place cx p s2 = (INL cur,s3) /\
     place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_ok cx e) /\
  eval_target_place cx t es = (INL p,stp) /\
  read_place cx p stp = (INL cur,stc) /\
  place_type_value cx p stc = (INL ptv,st) /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  (do tv <- eval_expr cx e; read_result cx tv od) st = (r1,st1) ==>
  expr_sim ctx func cenv cx ty e st /\ expr_res_ok r1 /\
  expr_sim_inv cenv cx env st1 /\
  (!rhs. r1 = INL rhs ==>
    word_value rhs /\ is_word_type (expr_type e) /\
    ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv rhs)
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  `body_expr_ok cx e` by metis_tac[] >>
  drule_all expr_body_pre_word_result >> strip_tac >>
  `expr_sim ctx func cenv cx ty e st` by metis_tac[body_expr_ok_def] >>
  simp[] >> metis_tac[exprSimSourceTheory.word_value_type_word]
QED

Theorem aug_place_memory_read_typed:
  expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings t = SOME info /\
  eval_target_place cx t es = (INL (MemoryPlace id path),st) /\
  read_place cx (MemoryPlace id path) st = (INL cur,st') /\
  stmt_state_rel ctx func cenv cx st s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
  is_word_type ty ==>
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur
Proof
  strip_tac >> drule_all aug_place_target_memory_live >> strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[aug_place_target_entry_typed] >>
  `st.scopes = es.scopes` by metis_tac[aug_place_target_scopes] >>
  gvs[place_ptr_rel_def] >>
  `tv0 = entry.type` by metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >>
  gvs[] >>
  `cur = v` by
    gvs[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
        lift_sum_def, return_def, read_memory_path_def] >>
  gvs[] >> drule mem_path_offset_sound >> strip_tac >>
  irule vyperPlaceStatePreservationTheory.evaluate_subscripts_type >>
  goal_assum (drule_at Any) >> simp[] >> qexists_tac `entry.value` >> simp[]
QED

Theorem aug_place_memory_access_ready:
  expr_sim_inv cenv cx env es /\ body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty t bop e) /\
  ((?bt fld. t = AttributeTarget bt fld) \/ (?bt key. t = SubscriptTarget bt key)) /\
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  eval_target_place cx t es = (INL (MemoryPlace id path),st) /\
  read_place cx (MemoryPlace id path) st = (INL cur,stc) /\
  place_type_value cx (MemoryPlace id path) stc = (INL ptv,stt) /\
  stmt_state_rel ctx func cenv cx st s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) ==>
  stc = st /\ stt = st /\ type_bits ty MOD 8 = 0 /\
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
       mload (w2n w) s = typed_val_to_w256 tv cur
Proof
  strip_tac >>
  `?info. supported_target_info tops bindings t = SOME info` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  drule aug_place_typing >> strip_tac >>
  `is_word_type ty` by metis_tac[exprSimSourceTheory.word_value_type_word] >>
  drule_all aug_place_memory_read_typed >> strip_tac >>
  drule_all aug_place_memory_load >> strip_tac >> gvs[] >>
  `type_bits ty MOD 8 = 0` by
    (irule well_formed_type_bits >> qexists_tac `get_tenv cx` >>
     simp[well_formed_type_def] >> metis_tac[]) >>
  metis_tac[read_place_state, place_type_value_state]
QED

Theorem aug_place_replace_read_error:
  !path tv a old v err.
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace v) = INR err ==>
    ?msg. err = TypeError msg
Proof
  Induct_on `path` >- simp[assign_subscripts_def] >>
  rpt gen_tac >> Cases_on `h`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >>
      Cases_on `a` >>
      simp[Once evaluate_subscripts_def, Once assign_subscripts_def] >>
      simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >~ [`array_set_index _ _ _ _ = INR _`]
      >- (gvs[vyperValueOperationTheory.array_set_index_def,
              vyperValueOperationTheory.array_index_def, AllCaseEqs(),
              listTheory.oEL_THM] >> metis_tac[]) >>
      first_x_assum drule_all >> simp[]) >>
  Cases_on `a` >>
  simp[Once evaluate_subscripts_def, Once assign_subscripts_def] >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem aug_place_memory_write_success:
  lookup_scopes id st.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  write_place cx (MemoryPlace id path) v st = (res,st') /\
  stmt_res_ok lctx res ==>
  res = INL ()
Proof
  strip_tac >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[write_place_def, get_scopes_def, bind_def, lift_option_type_def,
       type_check_def, assert_def, lift_sum_def, set_scopes_def,
       return_def, raise_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope id st.scopes` >>
  gvs[return_def, raise_def, stmt_res_ok_def] >>
  rename1 `find_containing_scope id st.scopes = SOME fc` >> PairCases_on `fc` >>
  `fc2 = entry` by metis_tac[vyperLookupTheory.find_containing_scope_lookup, optionTheory.SOME_11] >>
  gvs[ignore_bind_def, bind_def, assert_def, return_def, raise_def,
      set_scopes_def, replace_memory_entry_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `assign_subscripts entry.type entry.value path (Replace v)` >>
  gvs[return_def, raise_def] >>
  drule_all aug_place_replace_read_error >> simp[]
QED

Theorem aug_place_memory_ptr_frame:
  place_ptr_rel cenv cx s0 (PlaceR (MemoryPlace id path)) w loc vt /\
  local_ptrs_reserved cenv sa /\
  (!x u. not_fresh_at sa x /\ lookup_var x s0 = SOME u ==>
         lookup_var x s = SOME u) ==>
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc vt
Proof
  simp[place_ptr_rel_def, local_ptrs_reserved_def] >>
  rpt strip_tac >>
  qexistsl_tac [`p`, `sz`, `b`, `t0`, `tv0`, `k`, `tv`, `t`] >>
  simp[] >>
  `not_fresh_at sa p` by metis_tac[] >> metis_tac[]
QED

Theorem aug_place_bop_write_result_ok:
  bop <> In /\ bop <> NotIn /\ stmt_res_ok lctx res /\
  (case bop_result cx ty bop [ty;expr_type e] cur rhs st of
     INR ex => res = INR ex /\ es' = st
   | INL v => write_place cx p v st = (res,es')) ==>
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs st =
   case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     NoneTV bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     NoneTV bop cur rhs` >> gvs[expr_res_ok_def, stmt_res_ok_def]
QED


(* x op= e at a field or element of a local: the place is in memory. *)
Theorem compile_augassign_place_memory_case:
  !ctx func cx lctx RetQ cenv ret_ty env env' tops bindings ty bt bop e es id.
    target_root bt = NameTarget id /\
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
