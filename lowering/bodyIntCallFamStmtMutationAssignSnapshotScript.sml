(* Assign's lowered-type capture boundary. *)
Theory bodyIntCallFamStmtMutationAssignSnapshot
Ancestors
  bodyIntCallJointContract bodyPtrIfExpSourceTyping
  exprPtrUnwrapStorageShape abiEncodeArgsSim abiEncodeMaterialize
  exprSimHyps valueCopyBytes context loweringPosts

Theorem intcall_assign_lowered_value:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
  compile_expr ce ty e sa = (vv,sb) /\
  eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx (post_value_type ce e) raw vv ee s ==>
  vv_holds ce cx (lowered_value_type ce e) raw
    (vv_with_type (lowered_value_type ce e) vv) ee s /\
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
       value_has_type tv v
Proof
  strip_tac >>
  `?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
        value_has_type tv v` by
    metis_tac[ifexp_source_lowered_typed] >>
  reverse conj_tac >- metis_tac[] >>
  Cases_on `vv`
  >- (gvs[vv_with_type_def, vv_holds_def] >>
      irule abi_args_rel_lowered_transport >> simp[] >>
      metis_tac[memoryValueTypingTheory.value_has_type_val_wf]) >>
  rename1 `LocatedValue ann p` >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `is_word_type (expr_type e)`
      >- (`lowered_value_type ce e = expr_type e` by
            (drule expr_body_pre_lowered_fits >>
             qmatch_goalsub_abbrev_tac `lt = et` >>
             Cases_on `lt` >> Cases_on `et` >>
             gvs[vyperTypeSystemTheory.arg_type_fits_def, compileEnvTheory.is_word_type_def] >>
             rpt strip_tac >> Cases_on `b` >> Cases_on `b'` >>
             gvs[vyperTypeSystemTheory.arg_type_fits_def,
                 compileEnvTheory.is_word_type_def] >>
             Cases_on `b` >> Cases_on `b''` >>
             gvs[vyperTypeSystemTheory.arg_type_fits_def,
                 compileEnvTheory.is_word_type_def]) >>
          gvs[vv_holds_def, vv_with_type_def]) >>
      `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
        metis_tac[expr_body_pre_lowered_fits] >>
      drule_all materialize_post_lowered_classify >> strip_tac
      >- gvs[vv_holds_def, vv_with_type_def] >>
      `post_value_type ce e = expr_type e \/
       post_value_type ce e = lowered_value_type ce e` by
        (Cases_on `e` >> simp[post_value_type_def] >>
         rename1 `Call _ ct _ _` >> Cases_on `ct` >>
         simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
         IF_CASES_TAC >> simp[]) >>
      `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
        metis_tac[expr_body_pre_type_evaluates, optionTheory.IS_SOME_EXISTS] >>
      gvs[vv_holds_def, vv_with_type_def, is_bytestring_word_type] >>
      rpt strip_tac >>
      irule bytestring_val_in_memory_transfer >> simp[] >>
      qexistsl [`post_value_type ce e`, `lowered_value_type ce e`,
                `get_tenv cx`, `ptv`] >> simp[]) >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[compile_nonmemory_lowered_value_type] >>
  `post_value_type ce e = expr_type e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ ct _ _` >> Cases_on `ct` >>
     simp[post_value_type_def, exprLoweringTheory.lowered_value_type_def,
          vyperASTTheory.expr_type_def] >> metis_tac[]) >>
  gvs[vv_holds_def, vv_with_type_def]
QED

(* Forcing consumes the lowered layout.  In precisely the nonbytes aggregate
   case that requires a producer window, that layout is the producer layout. *)
Theorem intcall_assign_unwrap_type:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
  type_alloc_ok ce (lowered_value_type ce e) ==>
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  (~is_word_type (lowered_value_type ce e) /\
   ~is_bytestring_type (lowered_value_type ce e) ==>
   post_value_type ce e = lowered_value_type ce e)
Proof
  strip_tac >>
  conj_tac
  >- (irule expr_sim_inv_memory_size >>
      gvs[exprSimHypsDefsTheory.expr_body_pre_def] >> metis_tac[]) >>
  conj_tac
  >- (gvs[allocLimitsTheory.type_alloc_ok_def] >>
      `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv` by
        (irule expr_sim_inv_memory_size >>
         gvs[exprSimHypsDefsTheory.expr_body_pre_def] >> metis_tac[]) >>
      Cases_on `is_word_type (lowered_value_type ce e)` >> gvs[] >>
      `type_memory_size tv = 32` by
        metis_tac[stmtSimReturnTheory.word_type_sizes] >> simp[]) >>
  strip_tac >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by
    metis_tac[exprSimLayoutTransportTheory.compatible_word_type] >>
  metis_tac[materialize_post_lowered_classify]
QED
