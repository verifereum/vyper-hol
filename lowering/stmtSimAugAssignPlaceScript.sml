(*
 * Augmented assignment to a field or an element of a place (#637): the
 * facts the memory and storage cases share.  The statement's typing, its
 * source steps (aug_place_eval_cases), the code's parts
 * (aug_place_code_parts), and the binop's readiness.
 *)
Theory stmtSimAugAssignPlace
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
  bodySimAugPlaceScopes
Libs
  monadsyntax

Theorem aug_place_local_pop_index_unsupported:
  !tops ty ety id key.
    ~supported_expr tops (Subscript ty (Pop ety (NameTarget id)) key)
Proof
  simp[supported_expr_def, supported_pure_expr_def,
       supported_effect_expr_def]
QED

Theorem aug_place_nested_pop_target_unsupported:
  !tops bindings ty ety id outer inner bop rhs.
    ~supported_stmt tops bindings
      (AugAssign ty
        (SubscriptTarget (SubscriptTarget (NameTarget id) outer)
          (Subscript ty (Pop ety (NameTarget id)) inner)) bop rhs)
Proof
  simp[supported_stmt_def, supported_aug_target_def,
       supportedTargetsTheory.supported_target_info_def, aug_place_local_pop_index_unsupported,
       supported_target_def]
QED

Theorem aug_place_read_memory_current:
  !entry path v.
    evaluate_subscripts entry.type entry.value path = INL v ==>
    read_memory_path entry path = INL v
Proof
  simp[read_memory_path_def]
QED

Theorem aug_place_typing:
  !env ret_ty ty t bop e env'.
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' ==>
    type_place_target env t = SOME (Type ty) /\
    well_typed_expr env e /\
    assignable_type env.type_defs ty /\
    assignable_type env.type_defs (expr_type e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    word_value_type ty /\ word_value_type (expr_type e) /\ env' = env
Proof
  rpt gen_tac >> simp[type_stmt_def, well_typed_target_def] >>
  strip_tac >> gvs[] >> metis_tac[well_typed_binop_augassign_word]
QED

Theorem aug_place_code_parts:
  !cenv lctx ret_ty ty t bop e sa c sf.
    stmt_env cenv lctx ret_ty (AugAssign ty t bop e) sa = (c,sf) ==>
    c = cenv /\
    ?r s0. compile_get_target_ptr compile_expr cenv t sa = (r,s0) /\
      ((FST (SND r) = NONE /\ emit_void INVALID [] s0 = ((),sf)) \/
       ?loc cur rhs result s1 s2 s3.
         FST (SND r) = SOME loc /\
         emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD)
           [FST r] s0 = (cur,s1) /\
         lower_value compile_expr cenv ty e s1 = (rhs,s2) /\
         compile_binop bop cur rhs ty NONE
           (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
         emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE)
           [FST r; result] s3 = ((),sf))
Proof
  rpt gen_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_get_target_ptr compile_expr cenv t sa` >>
  rename1 `compile_get_target_ptr _ _ _ _ = (ptr_result,cstart)` >>
  Cases_on `FST (SND ptr_result)` >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] 
  >- (Cases_on `emit_void INVALID [] cstart` >> simp[oneTheory.one]) >>
  rename1 `FST (SND ptr_result) = SOME loc` >>
  Cases_on `emit_op (case loc of LocStorage => SLOAD | LocTransient => TLOAD | _ => MLOAD) [FST ptr_result] cstart` >>
  rename1 `_ = (cur,s1)` >> simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs,s2)` >> simp[] >>
  Cases_on `compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2` >>
  rename1 `compile_binop _ _ _ _ _ _ _ = (result,cstore)` >>
  simp[] >>
  Cases_on `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE | _ => MSTORE) [FST ptr_result; result] cstore` >>
  simp[oneTheory.one]
QED

Theorem aug_place_eval_cases:
  eval_stmt cx (AugAssign ty t bop e) es = (res,es') ==>
  ?rp stp. eval_target_place cx t es = (rp,stp) /\
    case rp of
      INR ex => res = INR ex /\ es' = stp
    | INL p => ?rc stc. read_place cx p stp = (rc,stc) /\
      case rc of
        INR ex => res = INR ex /\ es' = stc
      | INL cur => ?rt stt. place_type_value cx p stc = (rt,stt) /\
        case rt of
          INR ex => res = INR ex /\ es' = stt
        | INL ptv => ?rr str.
          (do tv <- eval_expr cx e; read_result cx tv od) stt = (rr,str) /\
          case rr of
            INR ex => res = INR ex /\ es' = str
          | INL rhs =>
            case evaluate_binop
              (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
              ptv bop cur rhs of
              INR err => res = INR (Error err) /\ es' = str
            | INL v => write_place cx p v str = (res,es')
Proof
  Cases_on `eval_target_place cx t es` >> rename1 `_ = (rp,stp)` >>
  Cases_on `rp` >>
  simp[Once evaluate_def, bind_def] >>
  rename1 `eval_target_place cx t es = (INL p,stp)` >>
  Cases_on `read_place cx p stp` >>
  rename1 `read_place cx p stp = (rread,sread)` >>
  Cases_on `rread` >> simp[] >>
  rename1 `read_place cx p stp = (INL vcur,sread)` >>
  Cases_on `place_type_value cx p sread` >>
  rename1 `place_type_value cx p sread = (rtype,stype)` >>
  Cases_on `rtype` >> simp[] >>
  rename1 `place_type_value cx p sread = (INL vtype,stype)` >>
  Cases_on `eval_expr cx e stype` >> rename1 `eval_expr cx e stype = (raw,sraw)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `eval_expr cx e stype = (INL vraw,sraw)` >>
  Cases_on `read_result cx vraw sraw` >> rename1 `read_result cx vraw sraw = (rrhs,srhs)` >>
  Cases_on `rrhs` >> simp[] >>
  rename1 `read_result cx vraw sraw = (INL vrhs,srhs)` >>
  qmatch_goalsub_abbrev_tac `evaluate_binop u vtype bop vcur vrhs` >>
  Cases_on `evaluate_binop u vtype bop vcur vrhs` >>
  simp[lift_sum_def, return_def, raise_def, ignore_bind_def]
QED

Theorem aug_place_eval_bop:
  bop <> In /\ bop <> NotIn /\
  ((bop = Eq \/ bop = NotEq) ==> !bs. cur <> BytesV bs) ==>
  (case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of
     INR err => res = INR (Error err) /\ es' = st
   | INL v => write_place cx p v st = (res,es')) =
  (case bop_result cx ty bop [ty;expr_type e] cur rhs st of
     INR ex => res = INR ex /\ es' = st
   | INL v => write_place cx p v st = (res,es'))
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs st =
   case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
    (irule bop_result_augassign >> metis_tac[]) >>
  simp[] >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
    ptv bop cur rhs` >> simp[]
QED

Theorem aug_place_binop_ready:
  type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\
  evaluate_type (get_tenv cx) ty = SOME tvcur /\ value_has_type tvcur cur /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvrhs /\
  value_has_type tvrhs rhs /\
  (bop = Exp ==> el = expr_int_literal e) /\
  (do tv <- eval_expr cx e; read_result cx tv od) st0 = (INL rhs,st1) ==>
  binop_frag ctx func cenv cx bop ty ty NONE el
    [ty;expr_type e] cur rhs st1
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  drule eval_expr_read_INL >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> rhs = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i)` by
    (strip_tac >> irule eval_expr_shift_amount >> metis_tac[]) >>
  `(bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n)` by
    (strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  irule exprSimBinopFragTheory.binop_frag_word_typed >> simp[] >> metis_tac[]
QED

Theorem aug_place_bop_res_ok:
  bop <> In /\ bop <> NotIn /\ stmt_res_ok lctx res /\
  (case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of
     INR err => res = INR (Error err) /\ es' = st
   | INL v => write_place cx p v st = (res,es')) ==>
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st)
Proof
  strip_tac >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs st) <=>
   expr_res_ok (case evaluate_binop
     (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
     ptv bop cur rhs of INL v => INL v | INR err => INR (Error err))` by
    (irule bop_result_augassign_res_ok >> simp[]) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
    ptv bop cur rhs` >> gvs[expr_res_ok_def, stmt_res_ok_def]
QED

Theorem aug_place_emit_void_grows:
  emit_void opc ops sa = ((),sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule emit_void_extends >> strip_tac >>
  irule cs_extends_same_block >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem aug_place_emit_op_grows:
  emit_op opc ops sa = (v,sb) ==> cs_extends sa sb
Proof
  strip_tac >> drule emit_op_extends >> strip_tac >>
  irule cs_extends_same_block >>
  gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem aug_place_target_ptr_not_label:
  compile_get_target_ptr cfn cenv t sa = (r,sb) /\
  ((?bt fld. t = AttributeTarget bt fld) \/ (?bt k. t = SubscriptTarget bt k)) ==>
  !l. FST r <> Label l
Proof
  strip_tac >> gvs[Once exprLoweringTheory.compile_get_target_ptr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
  >- (drule exprSafeOperandTheory.emit_op_safe_operand >>
      simp[exprSafeOperandTheory.safe_operand_def]) >>
  Cases_on `SND (SND result)` >> gvs[]
  >>~- ([`SOME pt`], Cases_on `pt` >> gvs[] >>
    gvs[comp_bind_def, comp_return_def] >>
    rpt (pairarg_tac >> gvs[]) >>
    metis_tac[exprSafeOperandBuiltinsTheory.subscript_pop_not_label]) >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  metis_tac[exprSafeOperandBuiltinsTheory.subscript_pop_not_label]
QED

Theorem aug_place_extend_name_memory:
  extend_place cx (PlaceR (MemoryPlace id path)) sb s = (INL out,st) ==>
  out = PlaceR (MemoryPlace id (path ++ [sb]))
Proof
  simp[extend_place_def, extend_memory_place_def, bind_def,
       ignore_bind_def, return_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem aug_place_name_root_base:
  !t id cx s out st.
    target_root t = NameTarget id /\
    eval_base_place cx t s = (INL out,st) ==>
    ?path. out = PlaceR (MemoryPlace id path)
Proof
  `(!e:expr. T) /\ (!t. !id cx s out st.
    target_root t = NameTarget id /\
    eval_base_place cx t s = (INL out,st) ==>
    ?path. out = PlaceR (MemoryPlace id path))` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[target_root_def] >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      metis_tac[])
  >> rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  gvs[] >> metis_tac[aug_place_extend_name_memory]
QED

Theorem aug_place_name_root_memory:
  target_root t = NameTarget id /\
  eval_target_place cx t es = (INL p,st) ==>
  ?path. p = MemoryPlace id path
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  drule_all aug_place_name_root_base >> strip_tac >>
  gvs[get_place_def, return_def]
QED

