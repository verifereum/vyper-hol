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
  vyperTypeBuiltins valueEncodingProps vyperExprNoControl gasContext targetPlaceSimDefs gasExemptCert gasSummary gasSummaryCompose gasOutcome
  exprSimSource bodyExprPreFacts exprSimTopLevelProps stmtSimBreak stmtSimContinue stmtSimExpr stmtSimSeqEnv stmtSimPass stmtSimProps exprSimHypsDefs stmtSimZero stmtSimDefs loweringPosts bodyAppendStorageFacts bodyAppendStorageAdapter
  vyperStorageLayoutSafety vyperLookupStorage
  list finite_map bodySim allocLimits allocLimitsProps  exprSimHyps exprLoweringProps
  stmtSimIf stmtLoweringMono stmtLowering compileEnv loweringStateRelDefs fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage stmtSimReasonCode supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  exprReasonOperand stmtSimDeclCompose
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
  stmtSimAugAssignPlace bodySimAugPlaceLoad bodySimAugPlaceLive bodySimAugPlaceScopes
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
      PURE_ONCE_REWRITE_TAC[evaluate_subscripts_def] >>
      PURE_ONCE_REWRITE_TAC[assign_subscripts_def] >>
      simp[AllCaseEqs()] >> rpt strip_tac >> gvs[]
      >~ [`array_set_index _ _ _ _ = INR _`]
      >- (gvs[vyperValueOperationTheory.array_set_index_def,
              vyperValueOperationTheory.array_index_def, AllCaseEqs(),
              listTheory.oEL_THM] >> metis_tac[]) >>
      first_x_assum drule_all >> simp[]) >>
  Cases_on `a` >>
  PURE_ONCE_REWRITE_TAC[evaluate_subscripts_def] >>
      PURE_ONCE_REWRITE_TAC[assign_subscripts_def] >>
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
  Cases_on `bop_result cx ty bop [ty;expr_type e] cur rhs st` >>
  gvs[expr_res_ok_def, stmt_res_ok_def] >>
  gvs[exprBopSimDefsTheory.bop_result_def, AllCaseEqs()]
QED


Theorem aug_place_rhs_pre_target:
  expr_body_pre cenv cx env e s /\ target_indices_pre cenv cx env t /\
  eval_target_place cx t s = (r,s') ==>
  expr_body_pre cenv cx env e s'
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env s` by fs[expr_body_pre_def] >>
  drule_all aug_place_target_inv >>
  fs[expr_body_pre_def]
QED

Theorem aug_place_rhs_pre_target_gas_obs:
  expr_body_pre cenv cx env e s /\ target_indices_pre cenv cx env t /\
  eval_target_place cx t (s with gas_obs := gs) = (r,s') ==>
  expr_body_pre cenv cx env e s'
Proof
  strip_tac >> irule aug_place_rhs_pre_target >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_target_bind_base:
  bind (eval_target_place cx bt) k =
  bind (eval_base_place cx bt) (\pv. bind (get_place pv) k)
Proof
  simp[Once evaluate_def, bind_assoc]
QED

Theorem aug_place_base_error_no_control:
  eval_base_place cx bt (es with gas_obs := gs) = (INR ex,ee) ==>
  no_control_exc ex
Proof
  metis_tac[eval_base_place_no_control]
QED

Theorem aug_place_base_admissible:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_res_ok_def] >>
  rename1 `eval_base_place cx bt _ = (INR ex,ee)` >>
  `no_control_exc ex` by metis_tac[aug_place_base_error_no_control] >>
  `eval_stmt cx (AugAssign ty bt bop e) (es with gas_obs := gs) =
   (INR ex,ee)` by
    (simp[Once evaluate_def, aug_place_target_bind_base, bind_def]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[] >>
  gvs[stmt_res_ok_def, target_res_ok_def, no_control_exc_def]
QED

Theorem aug_place_base_error_cert:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_base_place cx bt) (return ())) (es,s0)
    marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0)
    marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  simp[Once evaluate_def, aug_place_target_bind_base] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Theorem aug_place_rhs_admissible_target_endpoint:
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  gas_marked_exec memory (ctx,func) (eval_target_place cx bt)
    (es,s0) marks (INL p) mid (OK t) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  strip_tac >> irule expr_body_pre_gas_admissible >>
  qexistsl [`cenv`, `env`] >>
  irule aug_place_rhs_pre_target_gas_obs >>
  fs[gas_marked_exec_def] >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_memory_reads_error_cert:
  read_place cx (MemoryPlace id path) es = (INL cur,es) /\
  place_type_value cx (MemoryPlace id path) es = (INL ptv,es) /\
  gas_exempt_cert memory tops (ctx,func) (k cur ptv) (es,s0)
    marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (bind (read_place cx (MemoryPlace id path))
      (\v. bind (place_type_value cx (MemoryPlace id path)) (k v)))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  fs[read_place_def, place_type_value_def, get_scopes_def, bind_def,
     return_def, lift_option_type_def, lift_sum_def, AllCaseEqs()] >>
  Cases_on `lookup_scopes id es.scopes` >>
  gvs[return_def, raise_def] >>
  rename1 `read_memory_path entry path` >>
  Cases_on `read_memory_path entry path` >>
  gvs[return_def, raise_def] >>
  Cases_on `subscripts_type entry.type path` >>
  gvs[return_def, raise_def] >>
  simp[read_place_def, place_type_value_def, bind_assoc] >>
  irule gas_exempt_cert_get_scopes >>
  simp[lift_option_type_def, lift_sum_def, bind_return] >>
  irule gas_exempt_cert_get_scopes >>
  simp[lift_option_type_def, bind_return]
QED

Theorem aug_place_rhs_reached:
  ((?s p s1 s2 cur s3 s4 ptv s5.
      eval_target_place cx bt s = (INL p,s1) /\
      read_place cx p s2 = (INL cur,s3) /\
      place_type_value cx p s4 = (INL ptv,s5)) ==>
    expr_sim_case F ctx func cenv cx e) /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  eval_target_place cx bt (es with gas_obs := gs) = (INL p,st) /\
  read_place cx p st = (INL cur,stc) /\
  place_type_value cx p stc = (INL ptv,stt) ==>
  expr_sim_case F ctx func cenv cx e /\ expr_body_pre cenv cx env e stt
Proof
  strip_tac >>
  `stc = st /\ stt = stc` by metis_tac[read_place_state, place_type_value_state] >>
  gvs[] >> conj_tac
  >- metis_tac[] >>
  metis_tac[aug_place_rhs_pre_target_gas_obs]
QED

Theorem aug_place_rhs_memory_live:
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  supported_target_info tops bindings bt = SOME info /\
  eval_target_place cx bt s = (INL (MemoryPlace id path),st) /\
  bind (eval_expr cx e) (read_result cx) st = (r,ee) ==>
  ?entry old. lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL old
Proof
  strip_tac >> drule_all aug_place_target_memory_live >> strip_tac >>
  `supported_expr tops e` by fs[supported_stmt_def] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac aug_place_supported_expr_scopes >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED

Theorem aug_place_store_entry_types:
  expr_sim_inv cenv cx env ee ==>
  !id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type
Proof
  metis_tac[aug_place_entry_type_agrees]
QED

Theorem aug_place_outcome_bind_value:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0)
    (\res mid t. ?v. res = INL v /\
       gas_outcome memory tops (ctx,func) (k v) (mid,t) Q R)
    (\res ee r. ?exc. res = INR exc /\ R (INR exc) ee r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  rw[gas_outcome_def, gas_summary_at_def]
  >- metis_tac[gas_marked_exec_bind_normal]
  >- metis_tac[gas_marked_exec_bind_normal]
  >- (qexists `marks ++ marks'` >> disj2_tac >>
      qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
      simp[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> fs[ignore_bind_def])
  >- metis_tac[gas_marked_exec_bind_exception] >>
  simp[ignore_bind_def, bind_assoc] >>
  metis_tac[gas_exempt_cert_error_value]
QED

Theorem aug_place_memory_write_gas_obs:
  write_place cx (MemoryPlace id path) v ee = (res,ff) ==>
  !tail. write_place cx (MemoryPlace id path) v (ee with gas_obs := tail) =
    (res,ff with gas_obs := tail)
Proof
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       lift_option_type_def, type_check_def, assert_def, lift_sum_def,
       set_scopes_def, return_def, raise_def] >>
  Cases_on `find_containing_scope id ee.scopes` >>
  simp[raise_def, return_def] >>
  rename1 `SOME q` >> PairCases_on `q` >> Cases_on `q2.assignable` >>
  gvs[assert_def, ignore_bind_def, bind_def, return_def, raise_def,
      set_scopes_def] >>
  Cases_on `replace_memory_entry q2 path v` >>
  gvs[lift_sum_def, bind_def, return_def, raise_def, set_scopes_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem aug_place_pure_suffix_gas_obs:
  bind (lift_sum bv) (write_place cx (MemoryPlace id path)) ee = (res,ff) ==>
  !tail. bind (lift_sum bv) (write_place cx (MemoryPlace id path))
    (ee with gas_obs := tail) = (res,ff with gas_obs := tail)
Proof
  Cases_on `bv` >> simp[lift_sum_def, bind_def, return_def, raise_def] >>
  metis_tac[aug_place_memory_write_gas_obs]
QED

Theorem aug_place_pure_suffix_admissible:
  gas_admissible (bind (lift_sum bv) (write_place cx (MemoryPlace id path))) A ee /\
  bind (lift_sum bv) (write_place cx (MemoryPlace id path)) ee = (res,ff) ==>
  A res
Proof
  strip_tac >> drule aug_place_pure_suffix_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >>
  fs[gas_admissible_def] >> metis_tac[]
QED

Theorem aug_place_path_edge_labels:
  gas_path_edge ctx func s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  rw[fragGasPathTheory.gas_path_edge_def] >>
  gvs[fragExecTheory.exit_result_def, venomStateTheory.jump_to_def] >>
  metis_tac[venomExecProofsTheory.step_inst_preserves_labels_always,
            venomExecPropsTheory.eval_phis_preserves_labels]
QED

Theorem aug_place_path_labels:
  !ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> t.vs_labels = s.vs_labels
Proof
  ho_match_mp_tac fragGasPathTheory.gas_path_ind >>
  rpt strip_tac >> gvs[fragExecTheory.exit_result_def] >>
  metis_tac[aug_place_path_edge_labels]
QED

Theorem aug_place_marked_path_labels:
  gas_marked_path memory ctx func s n (OK t) ==> t.vs_labels = s.vs_labels
Proof
  metis_tac[fragGasModeTheory.gas_marked_path_exec, aug_place_path_labels]
QED

Theorem aug_place_saved_operand:
  gas_marked_path memory ctx func s n (OK t) /\
  (!z u. not_fresh_at cs z /\ lookup_var z s = SOME u ==>
         lookup_var z t = SOME u) /\
  (!z. dst = Var z ==> not_fresh_at cs z) /\
  eval_operand dst s = SOME w ==> eval_operand dst t = SOME w
Proof
  strip_tac >> drule aug_place_marked_path_labels >> strip_tac >>
  Cases_on `dst` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]
QED

Theorem aug_place_binop_store_outcome:
  bop <> In /\ bop <> NotIn /\
  ((bop = Eq \/ bop = NotEq) ==> !bs. cur <> BytesV bs) /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  emit_void MSTORE [dst;op] s3 = ((),sf) /\
  binop_frag ctx func cenv cx bop ty ty NONE el [ty;expr_type e] cur rhs ee /\
  gas_admissible
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (MemoryPlace id path)))
    (stmt_res_ok lctx) ee /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at s2 z) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
  stmt_state_rel ctx func cenv cx ee s /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  storage_place_region cx (MemoryPlace id path) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
       value_has_type dtv v) /\
  lookup_scopes id ee.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL old /\
  ~s.vs_halted /\ s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z s = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) /\
  (!v ff t. write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
           lookup_var z t = SOME u) /\
    (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts ==>
    stmt_post ctx func cx lctx cenv cenv sa sf s_entry
      (INL ()) (ff with gas_obs := []) t) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (MemoryPlace id path))) (ee,s)
    (stmt_post ctx func cx lctx cenv cenv sa sf s_entry)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ k _ _ _` >>
  Cases_on `k ee` >> rename1 `k ee = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (unabbrev_all_tac >> drule_all aug_place_pure_suffix_admissible >> simp[]) >>
  `case bop_result cx ty bop [ty;expr_type e] cur rhs ee of
     INR ex => res = INR ex /\ ff = ee
   | INL v => write_place cx (MemoryPlace id path) v ee = (res,ff)` by
    (`bop_result cx ty bop [ty;expr_type e] cur rhs ee =
      case evaluate_binop
        (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
        ptv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
       (irule bop_result_augassign >> metis_tac[]) >>
     simp[] >>
     qpat_x_assum `k ee = _` mp_tac >>
     simp[Abbr `k`, bind_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
       ptv bop cur rhs` >> simp[return_def, raise_def] >> metis_tac[]) >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee)` by
    (irule aug_place_bop_write_result_ok >> metis_tac[]) >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprBopSimDefsTheory.binop_frag_def,
                          exprBopSimDefsTheory.binop_frag_words_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `x`, `y`, `op`, `s`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >- suspend "normal" >> suspend "exit"
QED

Resume aug_place_binop_store_outcome[normal]:
  gvs[] >> rename1 `eval_operand op t = SOME (val_to_w256 v)` >>
  `res = INL ()` by (irule aug_place_memory_write_success >> metis_tac[]) >>
  gvs[] >>
  `place_ptr_rel cenv cx t (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand dst t = SOME w` by
    (irule aug_place_saved_operand >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `expr_val_rel cx ty v op t` by
    simp[expr_val_rel_def, typed_val_to_w256_word_value] >>
  `!j ps ent t0. MemoryPlace id path = MemoryPlace j ps /\
      lookup_scopes j ee.scopes = SOME ent /\ cenv.ce_var_type j = SOME t0 ==>
      evaluate_type (get_tenv cx) t0 = SOME ent.type` by
    (rpt strip_tac >> gvs[] >> irule aug_place_entry_type_agrees >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `!z. dst = Var z ==> not_fresh_at s3 z` by metis_tac[] >>
  drule_all (place_store_word_run |> SPEC_ALL |> Q.INST [`loc` |-> `LocMemory`] |> SIMP_RULE (srw_ss()) []) >>
  strip_tac >>
  `gas_marked_path F ctx func s 0 (OK t')` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  `stmt_post ctx func cx lctx cenv cenv sa sf s_entry
     (INL ()) (ff with gas_obs := []) t'` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `!tail. k (ee with gas_obs := tail) = (INL (),ff with gas_obs := tail)` by
    (unabbrev_all_tac >> drule aug_place_pure_suffix_gas_obs >> simp[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`, `ff`, `OK t'`] >> simp[]
QED

Resume aug_place_binop_store_outcome[exit]:
  `?ex. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INR ex` by
    (Cases_on `bop_result cx ty bop [ty;expr_type e] cur rhs ee` >>
     gvs[expr_exit_def]) >>
  gvs[] >>
  `!tail. k (ee with gas_obs := tail) = (INR ex,ee with gas_obs := tail)` by
    (unabbrev_all_tac >> drule aug_place_pure_suffix_gas_obs >> simp[]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INR ex`, `ee`, `r`] >> simp[stmt_exit_def] >>
  disj2_tac >> gen_tac >> disj1_tac >>
  Cases_on `ex` >> Cases_on `r` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >> gvs[expr_exit_def]
QED

Finalise aug_place_binop_store_outcome

Theorem aug_place_rhs_suffix_ready:
  expr_body_pre cenv cx env e st /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\ evaluate_type (get_tenv cx) ty = SOME dtv /\
  value_has_type dtv cur /\
  bind (eval_expr cx e) (read_result cx) st = (INL rhs,ee) ==>
  expr_sim_inv cenv cx env ee /\
  binop_frag ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE)
    [ty;expr_type e] cur rhs ee /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
       value_has_type dtv v)
Proof
  strip_tac >> drule aug_place_typing >> strip_tac >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule aug_place_binop_ready >> simp[] >> metis_tac[]) >>
  gen_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur rhs ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     dtv bop cur rhs of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >>
     metis_tac[word_value_not_bytes, word_value_type_typed]) >>
  pop_assum SUBST1_TAC >> simp[AllCaseEqs()] >> strip_tac >>
  irule well_typed_binop_success_type >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`ty`, `expr_type e`] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`get_tenv cx`, `dtv`, `ty`] >> simp[]
QED

Theorem aug_place_normal_post:
  ~block_is_terminated sf /\ stmt_state_rel ctx func cenv cx ff t /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z t = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP t.vs_allocas aid = SOME b) /\
  ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
  t.vs_inst_idx = LENGTH sf.cs_current_insts ==>
  stmt_post ctx func cx lctx cenv cenv sa sf s_entry (INL ()) ff t
Proof
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_def]
QED

Theorem aug_place_var_frame_trans[local]:
  (!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
         lookup_var z s1 = SOME a) /\
  (!z. not_fresh_at sa z ==> not_fresh_at sb z) /\
  (!z a. not_fresh_at sb z /\ lookup_var z s1 = SOME a ==>
         lookup_var z s2 = SOME a) ==>
  !z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
        lookup_var z s2 = SOME a
Proof
  metis_tac[]
QED

Theorem aug_place_alloca_frame_trans[local]:
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
           FLOOKUP s2.vs_allocas aid = SOME b) ==>
  !aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
          FLOOKUP s2.vs_allocas aid = SOME b
Proof
  metis_tac[]
QED

Theorem aug_place_store_post[local]:
  ~block_is_terminated sf ==>
  !v ff t. write_place cx (MemoryPlace id path) v ee = (INL (),ff) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
           lookup_var z t = SOME u) /\
    (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
    t.vs_inst_idx = LENGTH sf.cs_current_insts ==>
    stmt_post ctx func cx lctx cenv cenv sa sf s_entry
      (INL ()) (ff with gas_obs := []) t
Proof
  rpt strip_tac >> irule aug_place_normal_post >>
  simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs]
QED

Theorem aug_place_outcome_exec_conseq[local]:
  gas_outcome memory tops (ctx,func) source (es,s) Q R /\
  (!marks res mid t.
     gas_marked_exec memory (ctx,func) source (es,s) marks res mid (OK t) /\
     Q res (mid with gas_obs := []) t ==>
     Q' res (mid with gas_obs := []) t) /\
  (!res mid r. R res mid r ==> R' res mid r) ==>
  gas_outcome memory tops (ctx,func) source (es,s) Q' R'
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem aug_place_outcome_with_exec:
  gas_outcome memory tops (ctx,func) a (es,s0) Q E ==>
  gas_outcome memory tops (ctx,func) a (es,s0)
    (\res mid t. Q res mid t /\
      ?marks raw. mid = raw with gas_obs := [] /\
        gas_marked_exec memory (ctx,func) a (es,s0) marks res raw (OK t)) E
Proof
  strip_tac >> irule aug_place_outcome_exec_conseq >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem aug_place_outcome_bind_value_exec[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0) P
    (\res ee r. ?ex. res = INR ex /\ E (INR ex) ee r) /\
  (!marks v raw t.
    gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) raw (OK t) /\
    P (INL v) (raw with gas_obs := []) t ==>
    gas_outcome memory tops (ctx,func) (k v) (raw with gas_obs := [],t) Q E) /\
  (!res mid t. P res mid t ==> ?v. res = INL v) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q E
Proof
  strip_tac >> irule aug_place_outcome_bind_value >>
  irule aug_place_outcome_exec_conseq >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem aug_place_marked_bind_tail:
  gas_admissible (bind a k) A es /\
  gas_marked_exec memory (ctx,func) a (es,s0) marks (INL v) mid (OK t) ==>
  gas_admissible (k v) A (mid with gas_obs := [])
Proof
  simp[gas_admissible_def, gas_marked_exec_def] >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings ++ gs` mp_tac) >>
  simp[bind_def] >> metis_tac[]
QED

Theorem aug_place_memory_type_read:
  expr_sim_inv cenv cx env es /\ st.scopes = es.scopes /\
  lookup_scopes id st.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) ==>
  ?ptv. evaluate_type (get_tenv cx) ty = SOME ptv /\
    place_type_value cx (MemoryPlace id path) st = (INL ptv,st)
Proof
  strip_tac >> gvs[place_ptr_rel_def] >>
  `tv0 = entry.type` by metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >>
  gvs[] >> drule mem_path_offset_sound >> strip_tac >>
  simp[place_type_value_def, get_scopes_def, bind_def,
       lift_option_type_def, return_def]
QED

Theorem aug_place_path_not_halted[local]:
  !ctx func s n r. gas_path ctx func s n r ==>
    !t. r = OK t ==> ~t.vs_halted
Proof
  Induct_on `gas_path` >> rw[] >> gvs[fragExecTheory.exit_result_def]
QED

Theorem aug_place_marked_path_not_halted:
  gas_marked_path memory ctx func s n (OK t) ==> ~t.vs_halted
Proof
  metis_tac[fragGasModeTheory.gas_marked_path_exec, aug_place_path_not_halted]
QED

(* x op= e at a field or element of a local: the place is in memory. *)
Theorem aug_place_mload_boundary[local]:
  emit_op MLOAD [dst] ca = (cur,cb) /\ fn_has_code ca cb func /\
  stmt_state_rel ctx func cenv cx st t /\ local_ptrs_reserved cenv ca /\
  ~t.vs_halted /\ t.vs_current_bb = ca.cs_current_bb /\
  t.vs_inst_idx = LENGTH ca.cs_current_insts /\
  eval_operand dst t = SOME w /\
  (!z. dst = Var z ==> not_fresh_at ca z) /\ mload (w2n w) t = word ==>
  ?u. gas_marked_path F ctx func t 0 (OK u) /\
      stmt_state_rel ctx func cenv cx st u /\
      eval_operand cur u = SOME word /\ eval_operand dst u = SOME w /\
      (!z. cur = Var z ==> not_fresh_at cb z) /\
      (!z. not_fresh_at ca z ==> lookup_var z u = lookup_var z t) /\
      u.vs_allocas = t.vs_allocas /\ u.vs_memory = t.vs_memory /\
      u.vs_labels = t.vs_labels /\ ~u.vs_halted /\
      u.vs_current_bb = cb.cs_current_bb /\
      u.vs_inst_idx = LENGTH cb.cs_current_insts /\ local_ptrs_reserved cenv cb
Proof
  strip_tac >>
  `!out. step_inst_base (mk_inst ca.cs_next_id MLOAD [dst] [out]) t =
     OK (update_var out word t)` by
    (gen_tac >> drule emitHelperPropsTheory.step_MLOAD >> simp[]) >>
  drule_all (emitHelperPropsTheory.emit_op_zero_path |> SPEC_ALL |>
    Q.INST [`opc` |-> `MLOAD`] |> SIMP_RULE (srw_ss()) [venomInstTheory.is_terminator_def]) >>
  strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString ca.cs_next_var)) word t)
    with vs_inst_idx := SUC t.vs_inst_idx` >>
  conj_tac >- simp[fragGasModeTheory.gas_marked_path_def] >>
  conj_tac
  >- (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
      simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `ca` >> simp[]) >>
  `local_ptrs_reserved cenv cb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `ca` >>
     gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def]) >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emitHelperTheory.emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
       FLOOKUP_UPDATE, not_fresh_at_def, venomStateTheory.eval_operand_def] >>
  Cases_on `dst` >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def,
      FLOOKUP_UPDATE, not_fresh_at_def]
QED

Theorem aug_place_replay_admissible[local]:
  gas_admissible whole A es /\
  (!gs. whole (es with gas_obs := prefix ++ gs) =
        suffix (mid with gas_obs := gs)) ==>
  gas_admissible suffix A (mid with gas_obs := [])
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `prefix ++ gs` mp_tac) >>
  simp[]
QED

Theorem aug_place_memory_source_replay[local]:
  (!gs. eval_target_place cx bt (es with gas_obs := prefix ++ gs) =
    (INL (MemoryPlace id path),mid with gas_obs := gs)) /\
  read_place cx (MemoryPlace id path) (mid with gas_obs := []) =
    (INL cur,mid with gas_obs := []) /\
  place_type_value cx (MemoryPlace id path) (mid with gas_obs := []) =
    (INL ptv,mid with gas_obs := []) /\
  (!gs. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := readings ++ gs) = (INL rhs,last with gas_obs := gs)) ==>
  !gs. eval_stmt cx (AugAssign ty bt bop e)
    (es with gas_obs := (prefix ++ readings) ++ gs) =
    bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      ptv bop cur rhs)) (write_place cx (MemoryPlace id path))
      (last with gas_obs := gs)
Proof
  strip_tac >>
  `!gs. read_place cx (MemoryPlace id path) (mid with gas_obs := gs) =
    (INL cur,mid with gas_obs := gs)` by
    (Cases_on `lookup_scopes id mid.scopes` >>
     gvs[read_place_def, get_scopes_def, bind_def, return_def,
         lift_option_type_def, lift_sum_def, raise_def] >>
     Cases_on `read_memory_path x path` >>
     gvs[return_def, raise_def]) >>
  `!gs. place_type_value cx (MemoryPlace id path) (mid with gas_obs := gs) =
    (INL ptv,mid with gas_obs := gs)` by
    (Cases_on `lookup_scopes id mid.scopes` >>
     gvs[place_type_value_def, get_scopes_def, bind_def, return_def,
         lift_option_type_def, lift_sum_def, raise_def] >>
     Cases_on `subscripts_type x.type path` >>
     gvs[return_def, raise_def]) >>
  gen_tac >> pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[Once evaluate_def, bind_def, Excl "APPEND_ASSOC"] >>
  qpat_x_assum `!gs. bind (eval_expr _ _) _ _ = _`
    (qspec_then `gs` mp_tac) >>
  Cases_on `eval_expr cx e (mid with gas_obs := readings ++ gs)` >>
  Cases_on `q` >> simp[bind_def] >> strip_tac >> simp[]
QED

Theorem aug_place_completed_value_prefix[local]:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> value evaluation_result)
    (es,s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func) (k v)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  rw[gas_outcome_def, gas_summary_at_def]
  >- metis_tac[gas_marked_exec_bind_normal]
  >- metis_tac[gas_marked_exec_bind_normal] >>
  qexists_tac `left ++ marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> fs[ignore_bind_def]
QED

Theorem aug_place_completed_result_prefix[local]:
  gas_marked_exec memory (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result)
    (es,s0) left (INL v) mid (OK t) /\
  gas_outcome memory tops (ctx,func) (k v)
    (mid with gas_obs := [],t) Q R ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  rw[gas_outcome_def, gas_summary_at_def]
  >- metis_tac[gas_marked_exec_bind_normal]
  >- metis_tac[gas_marked_exec_bind_normal] >>
  qexists_tac `left ++ marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> fs[ignore_bind_def]
QED

Theorem aug_place_memory_reads_outcome[local]:
  read_place cx (MemoryPlace id path) st = (INL cur,st) /\
  place_type_value cx (MemoryPlace id path) st = (INL ptv,st) /\
  gas_outcome memory tops (ctx,func) (k cur ptv) (st,s) Q R ==>
  gas_outcome memory tops (ctx,func)
    (bind (read_place cx (MemoryPlace id path))
      (\v. bind (place_type_value cx (MemoryPlace id path)) (k v)))
    (st,s) Q R
Proof
  strip_tac >>
  `!gs. read_place cx (MemoryPlace id path) (st with gas_obs := gs) =
    (INL cur,st with gas_obs := gs)` by
    (Cases_on `lookup_scopes id st.scopes` >>
     gvs[read_place_def, get_scopes_def, bind_def, return_def,
         lift_option_type_def, lift_sum_def, raise_def] >>
     Cases_on `read_memory_path x path` >> gvs[return_def, raise_def]) >>
  `!gs. place_type_value cx (MemoryPlace id path) (st with gas_obs := gs) =
    (INL ptv,st with gas_obs := gs)` by
    (Cases_on `lookup_scopes id st.scopes` >>
     gvs[place_type_value_def, get_scopes_def, bind_def, return_def,
         lift_option_type_def, lift_sum_def, raise_def] >>
     Cases_on `subscripts_type x.type path` >> gvs[return_def, raise_def]) >>
  gvs[gas_outcome_def, gas_summary_at_def]
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_marked_exec_def, bind_def] >> metis_tac[])
  >- (qexists_tac `marks` >> disj1_tac >>
      fs[gas_marked_exec_def, bind_def] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (aug_place_memory_reads_error_cert |> SPEC_ALL |> Q.INST
    [`k` |-> `\v pt. ignore_bind (h v pt) (return ())`] |>
    CONV_RULE (DEPTH_CONV BETA_CONV) |>
    REWRITE_RULE [ignore_bind_def, bind_assoc]) >>
  goal_assum (drule_at Any) >> fs[ignore_bind_def]
QED

Theorem aug_place_memory_outer_outcome[local]:
  gas_marked_exec F (ctx,func) (eval_base_place cx bt)
    (es,s0) marks (INL (PlaceR (MemoryPlace id path))) raw (OK t) /\
  gas_marked_path F ctx func t 0 (OK u) /\
  read_place cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL cur,raw with gas_obs := []) /\
  place_type_value cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL ptv,raw with gas_obs := []) /\
  gas_outcome F tops (ctx,func) (k cur ptv)
    (raw with gas_obs := [],u) Q R ==>
  gas_outcome F tops (ctx,func)
    (bind (eval_target_place cx bt) (\p.
      bind (read_place cx p) (\v. bind (place_type_value cx p) (k v))))
    (es,s0) Q R
Proof
  strip_tac >> rewrite_tac[aug_place_target_bind_base] >>
  irule aug_place_completed_result_prefix >>
  goal_assum (drule_at Any) >>
  simp[get_place_def, bind_return] >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  irule aug_place_memory_reads_outcome >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_memory_outer_place_outcome[local]:
  gas_marked_exec F (ctx,func) (eval_base_place cx bt)
    (es,s0) marks (INL (PlaceR (MemoryPlace id path))) raw (OK t) /\
  gas_marked_path F ctx func t 0 (OK u) /\
  read_place cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL cur,raw with gas_obs := []) /\
  place_type_value cx (MemoryPlace id path) (raw with gas_obs := []) =
    (INL ptv,raw with gas_obs := []) /\
  gas_outcome F tops (ctx,func) (k (MemoryPlace id path) cur ptv)
    (raw with gas_obs := [],u) Q R ==>
  gas_outcome F tops (ctx,func)
    (bind (eval_target_place cx bt) (\p.
      bind (read_place cx p) (\v. bind (place_type_value cx p) (k p v))))
    (es,s0) Q R
Proof
  strip_tac >> rewrite_tac[aug_place_target_bind_base] >>
  irule aug_place_completed_result_prefix >>
  goal_assum (drule_at Any) >>
  simp[get_place_def, bind_return] >>
  irule gas_outcome_zero_prefix >> goal_assum (drule_at Any) >>
  irule aug_place_memory_reads_outcome >>
  goal_assum (drule_at Any) >> simp[]
QED

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
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `?info. supported_target_info tops bindings bt = SOME info` by
    (drule_all aug_place_supported_stmt_target_info >> simp[]) >>
  qpat_x_assum `(?b fld. bt = AttributeTarget b fld) \/ _` kall_tac >>
  drule aug_place_typing >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all aug_place_code_parts >> strip_tac >> gvs[] >>
  `cs_extends sa s0'` by
    (qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `compile_get_target_ptr _ _ target _` >>
     qspecl_then [`compile_expr`, `target`, `cenv`, `sa`]
       mp_tac ci_mono_compile_get_target_ptr_cfn >>
     simp[cj 1 compile_expr_ci_mono, ci_mono_def] >>
     rpt strip_tac >> gvs[]) >>
  `cs_extends s0' sb` by
    (imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
     imp_res_tac (cj 2 compile_expr_grows) >>
     imp_res_tac compile_binop_grows >>
     fs[cs_appends_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s0' func` by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `target_sim ctx func cenv cx env bt es` by
    (fs[target_case_def, target_pre_def]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[aug_place_base_admissible] >>
  qpat_x_assum `target_sim _ _ _ _ _ _ _` mp_tac >>
  simp[target_sim_def] >>
  disch_then (qspecl_then [`sa`, `s0'`, `r`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >> drule aug_place_outcome_with_exec >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  rewrite_tac[gas_outcome_def] >>
  (strip_tac >- suspend "base_completed" >> suspend "base_exempt")
QED

Resume compile_augassign_place_memory_case[base_exempt]:
  markerLib.RESUME_TAC >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[Once evaluate_def, aug_place_target_bind_base,
       ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[]
QED

Resume compile_augassign_place_memory_case[base_completed]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  (strip_tac >- suspend "base_normal" >> suspend "base_exit")
QED

Resume compile_augassign_place_memory_case[base_exit]:
  markerLib.RESUME_TAC >>
  Cases_on `res` >> fs[expr_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR ex) _ _` >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `r''`] >>
  (conj_tac
   >- (simp[Once evaluate_def, aug_place_target_bind_base] >>
       irule gas_marked_exec_bind_exception >> simp[])) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_place_memory_case[base_normal]:
  markerLib.RESUME_TAC >> gvs[] >>
  (Cases_on `FST (SND r) = NONE`
   >- (fs[target_post_def] >> Cases_on `pv` >>
       fs[place_ptr_rel_def] >> rename1 `PlaceR p` >>
       Cases_on `p` >> fs[place_ptr_rel_def])) >> gvs[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` kall_tac >>
  qpat_x_assum `es_end with gas_obs := [] = _` kall_tac >>
  `?path. pv = PlaceR (MemoryPlace id path)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     metis_tac[aug_place_name_root_base]) >> gvs[] >>
  `!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks' s0.vs_gas_readings ++ tail) =
      (INL (MemoryPlace id path), raw with gas_obs := tail)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     simp[Once evaluate_def, bind_def, get_place_def, return_def]) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[target_post_def, place_readable_def] >> strip_tac >>
  `loc = LocMemory` by (fs[place_ptr_rel_def] >> metis_tac[optionTheory.SOME_11]) >> gvs[] >>
  `expr_body_pre cenv cx env e (raw with gas_obs := [])` by
    (irule aug_place_rhs_pre_target_gas_obs >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     first_x_assum (qspec_then `[]` assume_tac) >> metis_tac[]) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  drule_all aug_place_target_memory_live >> strip_tac >>
  `expr_sim_inv cenv cx env (raw with gas_obs := [])` by
    fs[expr_body_pre_def] >>
  `?ptv. evaluate_type (get_tenv cx) ty = SOME ptv /\
     place_type_value cx (MemoryPlace id path) (raw with gas_obs := []) =
       (INL ptv,raw with gas_obs := [])` by
    (irule aug_place_memory_type_read >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  `expr_sim_case F ctx func cenv cx e` by
    (qpat_x_assum `(?s p s1 s2 cur s3 s4 ptv s5. _) ==> _` irule >>
     metis_tac[]) >>
  qpat_x_assum `(?s p s1 s2 cur s3 s4 ptv s5. _) ==> _` kall_tac >>
  qpat_x_assum `target_case _ _ _ _ _ _` kall_tac >>
  `is_word_type ty` by metis_tac[exprSimSourceTheory.word_value_type_word] >>
  `expr_sim_inv cenv cx env
     (es with gas_obs := gas_explicit marks' s0.vs_gas_readings ++ [])` by simp[] >>
  `stmt_state_rel ctx func cenv cx (raw with gas_obs := []) t` by simp[] >>
  drule_all aug_place_memory_load >> strip_tac >> gvs[] >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  `expr_sim_inv cenv cx env
     (es with gas_obs := gas_explicit marks' s0.vs_gas_readings ++ [])` by simp[] >>
  `stmt_state_rel ctx func cenv cx (raw with gas_obs := []) t` by simp[] >>
  drule_all aug_place_memory_read_typed >> strip_tac >> gvs[] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `cs_extends s3 sb /\ cs_extends s0' s1` by
    (simp[cs_extends_def] >> conj_tac >> qexists_tac `[]` >>
     fs[same_blocks_def]) >>
  `cs_extends s1 sb` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `fn_has_code s0' s1 func` by metis_tac[fn_has_code_split] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule aug_place_marked_path_not_halted >> simp[]) >>
  `local_ptrs_reserved cenv s0'` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >>
     qspecl_then [`bt`, `cenv`, `sa`] mp_tac
       stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  drule_all aug_place_mload_boundary >> strip_tac >>
  `place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >> qexistsl_tac [`t`, `s0'`] >> simp[]) >>
  `word_value v` by
    (drule_all exprSimSourceTheory.word_value_type_typed >> simp[]) >>
  `eval_operand cur u = SOME (val_to_w256 v)` by
    fs[typed_val_to_w256_word_value] >>
  `expr_body_pre cenv cx env e (raw with gas_obs := [])` by
    fs[expr_body_pre_gas_obs] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx))
     expr_res_ok (raw with gas_obs := [])` by
    (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  `fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `expr_sim ctx func cenv cx ty e (raw with gas_obs := [])` by
    (qpat_x_assum `expr_sim_case F _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_sim_case_def] >>
     disch_then (qspecl_then [`env`, `ty`, `raw with gas_obs := []`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `expr_sim ctx func cenv cx ty e _` mp_tac >>
  pure_rewrite_tac[expr_sim_def] >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs`, `u`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  drule aug_place_outcome_with_exec >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
  rewrite_tac[gas_outcome_def] >>
  (strip_tac >- suspend "rhs_completed" >> suspend "rhs_exempt")
QED

Resume compile_augassign_place_memory_case[rhs_completed]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_summary_at_def] >>
  (strip_tac >- suspend "rhs_normal" >> suspend "rhs_exit")
QED

Resume compile_augassign_place_memory_case[rhs_normal]:
  gvs[] >>
  qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` kall_tac >>
  qpat_x_assum `es_end with gas_obs := [] = _` kall_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (raw with gas_obs := gas_explicit marks'' u.vs_gas_readings) =
     (INL v'',raw' with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ _ _ marks'' _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env e
     (raw with gas_obs := gas_explicit marks'' u.vs_gas_readings)` by
    simp[expr_body_pre_gas_obs] >>
  `type_bits ty MOD 8 = 0` by
    (irule well_formed_type_bits >> qexists_tac `get_tenv cx` >>
     simp[well_formed_type_def] >> metis_tac[]) >>
  drule_all aug_place_rhs_suffix_ready >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_post_def] >> strip_tac >>
  `gas_marked_path F ctx func u (LENGTH marks'') (OK t')` by
    (qpat_assum `gas_marked_exec _ _ _ _ marks'' _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand cur t' = SOME (val_to_w256 v)` by
    (irule aug_place_saved_operand >>
     goal_assum (drule_at Any) >>
     qexists_tac `s1` >> simp[]) >>
  `?entry old. lookup_scopes id (raw' with gas_obs := []).scopes = SOME entry /\
     evaluate_subscripts entry.type entry.value path = INL old` by
    (irule aug_place_rhs_memory_live >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     qexists_tac `es with gas_obs :=
       gas_explicit marks' s0.vs_gas_readings ++
       gas_explicit marks'' u.vs_gas_readings` >> simp[]) >>
  `place_ptr_rel cenv cx t' (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >> qexistsl_tac [`u`, `s1`] >> simp[]) >>
  `s0'.cs_next_var <= s1.cs_next_var` by
    (qspec_then `MLOAD` mp_tac (CONJUNCT1 exprOperandVarTheory.compiler_counter_emit) >>
     disch_then (qspecl_then [`[FST r]`, `s0'`] mp_tac) >> simp[]) >>
  `!z. FST r = Var z ==> not_fresh_at s1 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (FST r) t' = SOME w` by
    (irule aug_place_saved_operand >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!gs. bind (eval_expr cx e) (read_result cx)
     (raw with gas_obs := gas_explicit marks'' u.vs_gas_readings ++ gs) =
     (INL v'',raw' with gas_obs := gs)` by
    (gen_tac >>
     qpat_assum `gas_marked_exec _ _ _ _ marks'' _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     qpat_x_assum `!tail. _` (qspec_then `gs` mp_tac) >> simp[]) >>
  `gas_admissible
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      ptv bop v v'')) (write_place cx (MemoryPlace id path)))
    (stmt_res_ok lctx) (raw' with gas_obs := [])` by
    (irule aug_place_replay_admissible >>
     goal_assum (drule_at Any) >>
     qexists_tac `gas_explicit marks' s0.vs_gas_readings ++
       gas_explicit marks'' u.vs_gas_readings` >>
     irule aug_place_memory_source_replay >>
     goal_assum (drule_at Any) >> simp[]) >>
  `sa.cs_next_var <= s0'.cs_next_var` by
    (qspecl_then [`bt`, `cenv`, `sa`] mp_tac
       stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
          lookup_var z t' = SOME a` by
    (match_mp_tac (aug_place_var_frame_trans |> Q.INST [`s1` |-> `u`] |> Q.INST [`sb` |-> `s1`]) >>
     simp[] >> rpt strip_tac >>
     `not_fresh_at s0' z` by
       (irule freshWritesTheory.not_fresh_at_mono >> goal_assum (drule_at Any) >> simp[]) >>
     simp[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t'.vs_allocas aid = SOME b` by
    (match_mp_tac (aug_place_alloca_frame_trans |> Q.INST [`s1` |-> `u`]) >> simp[]) >>
  `!z. rhs = Var z ==> not_fresh_at s2 z` by
    (drule_at (Pos hd) exprOperandVarTheory.compile_lower_value_var >>
     simp[]) >>
  `!z. cur = Var z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z. FST r = Var z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z. not_fresh_at sa z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z. not_fresh_at s2 z ==> not_fresh_at s3 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >> simp[]) >>
  `local_ptrs_reserved cenv s3` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s2` >> simp[]) >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  `~t'.vs_halted` by metis_tac[aug_place_marked_path_not_halted] >>
  `word_value v'' /\ ?tyv.
     evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
     value_has_type tyv v''` by
    (qpat_assum `expr_body_pre _ _ _ _ (_ with gas_obs := gas_explicit _ _)` mp_tac >>
     qpat_assum `word_value_type (expr_type e)` mp_tac >>
     qpat_assum `_ = (INL v'',raw' with gas_obs := [])` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_word_result, ETA_THM]) >>
  `is_word_type (expr_type e)` by metis_tac[word_value_type_word] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  gvs[] >>
  `eval_operand rhs t' = SOME (val_to_w256 v'')` by
    (irule exprBopSimPropsTheory.expr_val_rel_word >> simp[] >>
     qexistsl_tac [`cx`, `expr_type e`] >> simp[]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `storage_place_region cx (MemoryPlace id path)` by
    simp[vyperStoragePlaceProvenanceTheory.storage_place_region_def] >>
  `~block_is_terminated sb` by
    (irule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
  drule aug_place_store_post >> disch_then assume_tac >>
  `(bop = Eq \/ bop = NotEq) ==> !bs. v <> BytesV bs` by
    (qpat_assum `word_value_type ty` mp_tac >>
     qpat_assum `evaluate_type (get_tenv cx) ty = SOME ptv` mp_tac >>
     qpat_assum `value_has_type ptv v` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[word_value_type_typed, word_value_not_bytes]) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
      ptv bop v v'')) (write_place cx (MemoryPlace id path)))
    (raw' with gas_obs := [],t')
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)` by
    (irule aug_place_binop_store_outcome >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     conj_tac >- (metis_tac[]) >>
     conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
     conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
     asm_simp_tac std_ss [] >>
     conj_tac >- (qexistsl_tac [`entry'`, `old`] >> simp[]) >>
     conj_tac >- (first_assum ACCEPT_TAC) >>
     conj_tac >- simp[gasContextTheory.gas_admissible_gas_obs] >>
     conj_tac >- (qexists_tac `env` >> simp[]) >>
     conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     asm_simp_tac std_ss [exprBopSimPropsTheory.bop_result_gas_obs] >>
     metis_tac[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)`
    suffices_by simp[gas_outcome_def, gas_summary_at_def] >>
  simp[Once evaluate_def] >>
  ho_match_mp_tac (GEN_ALL aug_place_memory_outer_place_outcome) >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_place _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_type_value _ _ _ = _`)) >>
  irule (aug_place_completed_value_prefix |> SPEC_ALL |>
    Q.INST [`a` |-> `bind (eval_expr cx e) (read_result cx)`] |>
    REWRITE_RULE [bind_assoc]) >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Resume compile_augassign_place_memory_case[rhs_exit]:
  markerLib.RESUME_TAC >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)`
    suffices_by simp[gas_outcome_def, gas_summary_at_def] >>
  simp[Once evaluate_def] >>
  ho_match_mp_tac (GEN_ALL aug_place_memory_outer_place_outcome) >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_place _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_type_value _ _ _ = _`)) >>
  Cases_on `res` >> fs[expr_exit_def] >>
  rename1 `gas_marked_exec _ _ _ _ _ (INR ex) _ _` >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `r'`] >>
  (conj_tac >- (rewrite_tac[GSYM bind_assoc] >>
    irule gas_marked_exec_bind_exception >> simp[])) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_place_memory_case[rhs_exempt]:
  markerLib.RESUME_TAC >>
  `gas_outcome F (cx_tops cx) (ctx,func)
    (eval_stmt cx (AugAssign ty bt bop e)) (es,s0)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)`
    suffices_by simp[gas_outcome_def, gas_summary_at_def] >>
  simp[Once evaluate_def] >>
  ho_match_mp_tac (GEN_ALL aug_place_memory_outer_place_outcome) >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `read_place _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_type_value _ _ _ = _`)) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (gas_exempt_cert_error_value |> SPEC_ALL |>
    Q.INST [`a` |-> `bind (eval_expr cx e) (read_result cx)`] |>
    REWRITE_RULE [ignore_bind_def, bind_assoc]) >>
  fs[ignore_bind_def, bind_assoc]
QED

Finalise compile_augassign_place_memory_case
