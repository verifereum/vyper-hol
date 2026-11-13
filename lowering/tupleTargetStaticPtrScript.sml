(* Static target obligations from the enclosing tuple assignment. *)
Theory tupleTargetStaticPtr
Ancestors
  bodyAugPlaceTarget bodyPtrPopCompose bodyPtrStructLitTupleFrame
  bodyExprPreFacts tupleTargetStoreProps bodySim supportedStmts supportedStmtTraverse
  exprSimHyps exprSimHypsDefs supportedTargets supportedExprForms targetPlaceSim
  allocLimits vyperTypeCallGraph vyperTypeCallStackSoundness
  vyperTypeSystem vyperAST list option

Theorem tuple_target_static_projection[local]:
  !gs.
    alloc_limits_assignments cenv gs /\
    ~supported_assignments_exists p gs /\
    call_evaluation_safe cx (int_calls_atargets gs) ==>
    EVERY (\g. alloc_limits_assignment cenv g /\
      ~supported_assignment_exists p g /\
      call_evaluation_safe cx (int_calls_atarget g)) gs
Proof
  Induct >> simp[alloc_limits_assignment_def,supported_assignment_exists_def,
    int_calls_atarget_def] >> rpt strip_tac >>
  metis_tac[call_evaluation_safe_append_left,call_evaluation_safe_append_right]
QED

Theorem tuple_supported_flat_target_pre[local]:
  body_inv tops ctx cenv cx /\ supported_target tops bindings bt /\
  IS_SOME (type_place_target env bt) /\ alloc_limits_target cenv bt /\
  ~supported_target_exists
    (\e. ~is_extcode e /\ ~(byte_widths_expr e /\ alloc_limits_expr cenv e)) bt /\
  call_evaluation_safe cx (int_calls_target bt) /\
  (!target. supported_target_exists (expr_abi_decode_target_root target) bt ==>
    occurs_abi_decode_target target tops) ==>
  target_indices_pre cenv cx env bt
Proof
  strip_tac >> Cases_on `bt`
  >- simp[target_indices_pre_def]
  >- simp[target_indices_pre_def]
  >- (rename1 `SubscriptTarget b key` >>
      `IS_SOME (supported_target_info tops bindings (SubscriptTarget b key))` by
        (gvs[supported_target_def] >> Cases_on `b` >> gvs[] >>
         irule aug_place_legacy_subscript_info >> fs[body_inv_def]) >>
      irule aug_place_target_indices_pre >> fs[body_inv_def] >>
      qexists_tac `bindings` >> simp[]) >>
  rename1 `AttributeTarget b fld` >>
  `IS_SOME (supported_target_info tops bindings (AttributeTarget b fld))` by
    (gvs[supported_target_def] >> Cases_on `b` >> gvs[] >>
     irule aug_place_legacy_field_info >> fs[body_inv_def]) >>
  irule aug_place_target_indices_pre >> fs[body_inv_def] >>
  qexists_tac `bindings` >> simp[]
QED

Theorem tuple_assignment_target_static_ptr:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  ~cenv.ce_is_ctor /\
  supported_stmt tops bindings (Assign (TupleTarget gs) e) /\
  type_stmt env ret_ty (Assign (TupleTarget gs) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (TupleTarget gs) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (TupleTarget gs) e)) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (TupleTarget gs) e) ==> occurs_abi_decode_target target tops) ==>
  EVERY (\g. ?bt. g = BaseTarget bt /\ supported_target tops bindings bt /\
    ~immutable_root cx bt /\ target_indices_pre cenv cx env bt /\
    call_evaluation_safe cx (int_calls_target bt)) gs
Proof
  strip_tac >> drule tuple_targets_typing >> strip_tac >>
  `EVERY (\g. alloc_limits_assignment cenv g /\
    ~supported_assignment_exists
      (\x. ~is_extcode x /\ ~(byte_widths_expr x /\ alloc_limits_expr cenv x)) g /\
    call_evaluation_safe cx (int_calls_atarget g)) gs` by
    (irule tuple_target_static_projection >>
     fs[stmt_exprs_ok_flat,alloc_limits_stmt_def,alloc_limits_assignment_def,
       supported_stmt_expr_exists_def,supported_assignment_exists_def,
       int_calls_stmt_def,int_calls_atarget_def] >>
     metis_tac[call_evaluation_safe_append_left]) >>
  simp[EVERY_EL] >> qx_gen_tac `i` >> strip_tac >>
  `well_typed_atarget env (EL i gs) (EL i tys)` by
    (fs[LIST_REL_EL_EQN] >> metis_tac[]) >>
  `case EL i gs of BaseTarget bt => supported_target tops bindings bt
    | TupleTarget _ => F` by
    fs[supported_stmt_def,supported_assignment_def,EVERY_EL] >>
  Cases_on `EL i gs` >> gvs[] >> rename1 `BaseTarget bt` >>
  `IS_SOME (type_place_target env bt)` by fs[tuple_target_base_type] >>
  `alloc_limits_target cenv bt /\
   ~supported_target_exists
     (\x. ~is_extcode x /\ ~(byte_widths_expr x /\ alloc_limits_expr cenv x)) bt /\
   call_evaluation_safe cx (int_calls_target bt)` by
    (qpat_assum `EVERY (\g. alloc_limits_assignment cenv g /\ _) gs`
       (mp_tac o REWRITE_RULE [EVERY_EL]) >>
     disch_then (qspec_then `i` mp_tac) >>
     simp[alloc_limits_assignment_def,supported_assignment_exists_def,
       int_calls_atarget_def]) >>
  conj_tac >- metis_tac[runtime_typed_target_not_immutable_ptr] >>
  conj_tac >- (irule tuple_supported_flat_target_pre >> asm_rewrite_tac[] >>
    qexistsl_tac [`bindings`,`ctx`,`tops`] >> asm_rewrite_tac[] >>
    qx_gen_tac `target` >> strip_tac >> first_x_assum irule >>
    simp[supported_stmt_expr_exists_def,supported_assignment_exists_def] >>
    metis_tac[assignments_exclude_base_target,EL_MEM]) >>
  first_assum ACCEPT_TAC
QED
