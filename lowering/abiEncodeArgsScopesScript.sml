Theory abiEncodeArgsScopes
Ancestors
  pair sum vyperMisc vyperContext vyperState vyperLookup
  exprLowering vyperInterpreter vyperScopePreservation vyperStatePreservation
  vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame
  vyperEvalExprPreservesScopesDom

Theorem exprs_can_mutate_exists:
  !ce es. exprs_can_mutate ce es = EXISTS (expr_can_mutate ce) es
Proof
  gen_tac >> Induct >> simp[expr_can_mutate_def]
QED

Theorem named_exprs_can_mutate_map:
  !ce kes. named_exprs_can_mutate ce kes = exprs_can_mutate ce (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[expr_can_mutate_def] >> Cases_on `h` >> simp[expr_can_mutate_def]
QED

Theorem exprs_no_mutation_take_drop:
  !ce es n. ~exprs_can_mutate ce es ==>
    ~exprs_can_mutate ce (TAKE n es) /\ ~exprs_can_mutate ce (DROP n es)
Proof
  gen_tac >> Induct_on `es` >> simp[expr_can_mutate_def] >>
  Cases_on `n` >> simp[expr_can_mutate_def]
QED

Theorem intcall_unlock_scopes[local]:
  !nr mut cx st res st'.
    (if nr /\ mut <> View /\ mut <> Pure then
       case cx.nonreentrant_slot of
       | NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) st = (res,st') ==> st'.scopes = st.scopes
Proof
  rpt gen_tac >> Cases_on `nr /\ mut <> View /\ mut <> Pure` >> simp[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[return_def] >>
  metis_tac[release_nonreentrant_lock_scopes]
QED

Theorem intcall_finally_scopes[local]:
  !f nr mut cx prev st res st'.
    finally f
      (bind (set_scopes prev) (\x.
        if nr /\ mut <> View /\ mut <> Pure then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ())) st = (res,st') ==> st'.scopes = prev
Proof
  rpt strip_tac >>
  gvs[finally_def, bind_def, ignore_bind_def, set_scopes_def,
      return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac intcall_unlock_scopes >> gvs[]
QED

Theorem intcall_acquire_scopes[local]:
  !cx nr v st res st'.
    lock_if_nr cx nr v st = (res,st') ==> st'.scopes = st.scopes
Proof
  rpt gen_tac >> Cases_on `nr` >> simp[lock_if_nr_def, return_def] >>
  Cases_on `cx.nonreentrant_slot` >> simp[raise_def, bind_def, ignore_bind_def] >>
  Cases_on `acquire_nonreentrant_lock cx.txn.target x (v \/ cx.txn.is_static) st` >>
  rename1 `_ = (r1,s1)` >>
  drule acquire_nonreentrant_lock_scopes >>
  Cases_on `r1` >> Cases_on `v` >> rw[return_def] >> gvs[]
QED

Theorem eval_no_mutation_scopes[local]:
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tv:type_value. !id:string. !body:stmt list. !vs:value list. T) /\
  (!cx e. !ce st res st'. ~expr_can_mutate ce e /\
    eval_expr cx e st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx es. !ce st res st'. ~exprs_can_mutate ce es /\
    eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes) /\
  (!cx:evaluation_context. !bt:base_assignment_target. T) /\
  (!cx:evaluation_context. !bt:base_assignment_target. T) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T) /\
  (!cx es. !ce st res st'. ~exprs_can_mutate ce es /\
    eval_expr_results cx es st = (res,st') ==> st'.scopes = st.scopes)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> simp[expr_can_mutate_def, call_can_mutate_def]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, lift_option_type_def, return_def, raise_def, AllCaseEqs()])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_global_scopes >> gvs[])
  >- (rpt strip_tac >> gvs[Once evaluate_def] >>
      imp_res_tac lookup_flag_mem_scopes >> gvs[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def,
          switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac conditional_result_state >> gvs[] >>
      gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[])
  >- (rpt strip_tac >> gvs[Once evaluate_def, return_def])
  >- (rpt strip_tac >> gvs[named_exprs_can_mutate_map] >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac read_result_state >> imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac select_result_state >> gvs[] >> metis_tac[])
  >- suspend "Builtin"
  >- suspend "TypeBuiltin"
  >- suspend "ExtCall"
  >- suspend "IntCall"
  >- suspend "RawCall"
  >- suspend "RawCallCalldata"
  >- suspend "RawLog"
  >- suspend "RawRevert"
  >- simp[Once evaluate_def, return_def]
  >- (rpt strip_tac >>
      gvs[expr_can_mutate_def, Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      imp_res_tac read_result_state >> gvs[] >> metis_tac[])
  >- simp[Once evaluate_def, return_def]
  >> rpt strip_tac >>
  gvs[expr_can_mutate_def, Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED

Resume eval_no_mutation_scopes[ExtCall]:
  rpt strip_tac >>
  imp_res_tac exprs_no_mutation_take_drop >>
  qpat_x_assum `eval_expr cx (Call _ (ExtCall _ _ _ _) _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> imp_res_tac eval_ext_call_preserves_non_accounts >>
  imp_res_tac read_results_state >> gvs[] >>
  `~exprs_can_mutate ce (TAKE (LENGTH (FST (SND sig))) (DROP 1 es))`
    by metis_tac[exprs_no_mutation_take_drop] >>
  metis_tac[]
QED

Resume eval_no_mutation_scopes[IntCall]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3. _` 
    (mp_tac o SRULE [type_check_def, assert_def, lift_option_type_def,
                     option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  disch_then assume_tac >>
  qpat_x_assum `!s t s1 ts t1 s2 tup t2 s3 t3 s4 vs t4 s5 prev t5 s6 t6. _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def, bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (drule type_check_scopes >> rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >> rw[] >> gvs[]) >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >> rw[] >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum `_ r' = (res,st')` mp_tac >>
  rewrite_tac[bind_def, ignore_bind_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac type_check_scopes >> imp_res_tac lift_option_type_scopes >> rw[] >> gvs[]) >>
  unabbrev_all_tac >>
  rule_assum_tac (SRULE [type_check_def, assert_def, lift_option_type_def,
                        option_CASE_rator, return_def, raise_def, AllCaseEqs()]) >>
  gvs[] >> BasicProvers.TOP_CASE_TAC >>
  rename1 `eval_expr_results cx es sa = (qr,sb)` >>
  `sb.scopes = sa.scopes` by metis_tac[] >>
  reverse (Cases_on `qr`)
  >- (rw[] >> gvs[]) >>
  simp[bind_def, ignore_bind_def, get_scopes_def, return_def] >>
  BasicProvers.TOP_CASE_TAC >> reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> drule finally_set_scopes >> simp[] >> strip_tac >> gvs[]) >>
  strip_tac >> imp_res_tac finally_set_scopes >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp[pop_function_def, push_function_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac lift_option_type_scopes >> imp_res_tac read_results_state >>
  imp_res_tac (REWRITE_RULE [lock_if_nr_def, ignore_bind_def] intcall_acquire_scopes) >>
  imp_res_tac intcall_finally_scopes >>
  gvs[]
QED

(* Drop the Builtin induction hypotheses (they mention Bop or Len) once the
   needed instances are derived, so the case splits below stay cheap. *)
val drop_builtin_ihs_tac =
  rpt (first_x_assum (fn th =>
    let
      val c = concl th
      fun has n = can (find_term (fn t => is_const t andalso
                                          fst (dest_const t) = n)) c
    in
      if (is_forall c orelse is_imp_only c) andalso (has "Bop" orelse has "Len")
      then kall_tac th else NO_TAC
    end));

Resume eval_no_mutation_scopes[Builtin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `builtin_args_length_ok bt (LENGTH es)`
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `bt = Len`
      >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
              assert_def, return_def, raise_def, AllCaseEqs()] >>
          imp_res_tac result_array_length_state >>
          imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
          imp_res_tac precompile_call_success_state >> gvs[] >>
          Cases_on `es` >> gvs[expr_can_mutate_def, builtin_args_length_ok_def] >>
          first_x_assum drule_all >> simp[]) >>
      Cases_on `bt = Env MsgGas`
      >- (gvs[] >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
          simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
               assert_def, return_def, raise_def, AllCaseEqs()] >>
          rpt strip_tac >>
          imp_res_tac next_gas_reading_state >>
          imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
          imp_res_tac precompile_call_success_state >> gvs[]) >>
      Cases_on `bt = Bop In \/ bt = Bop NotIn`
      >- (`bt <> Len /\ bt <> Env MsgGas` by (strip_tac >> gvs[]) >>
          `!st res st'. eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes` by
            (rpt strip_tac >>
             qpat_x_assum `!s'' t. _ /\ bt <> Len /\ (bt = Bop In \/ bt = Bop NotIn) ==> _`
               (qspecl_then [`st`,`st`] mp_tac) >>
             simp[type_check_def, assert_def] >> metis_tac[]) >>
          drop_builtin_ihs_tac >>
          qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
          simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
               assert_def, return_def, raise_def, AllCaseEqs()] >>
          rpt strip_tac >>
          gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def,
              AllCaseEqs()] >>
          imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >>
          gvs[] >> metis_tac[]) >>
      Cases_on `code_slice_source bt es`
      >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
          qpat_assum `code_slice_source _ _ = _` (fn th1 =>
            qpat_assum `builtin_args_length_ok _ _` (fn th2 =>
              simp[Once evaluate_def, th1, th2, bind_def, ignore_bind_def,
                   type_check_def, assert_def, return_def, raise_def,
                   AllCaseEqs()])) >>
          rpt strip_tac >>
          imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
          imp_res_tac precompile_call_success_state >>
          gvs[expr_can_mutate_def, type_check_def, assert_def] >> metis_tac[]) >>
      PairCases_on `x` >>
      `?n start len. bt = Slice n /\
                     es = [Builtin x0 (Acc Code) [x1]; start; len]` by
        gvs[code_slice_source_SOME] >>
      gvs[expr_can_mutate_def, type_check_def, assert_def] >>
      qpat_x_assum `eval_expr _ (Builtin _ _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, return_def, raise_def, builtin_args_length_ok_def,
           AllCaseEqs()] >>
      rpt strip_tac >>
      imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
      imp_res_tac precompile_call_success_state >> gvs[] >>
      metis_tac[])
  >> simp[Once evaluate_def, type_check_def, assert_def, bind_def, ignore_bind_def, raise_def]
QED

Resume eval_no_mutation_scopes[TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  Cases_on `type_builtin_args_length_ok tb (LENGTH es)` >> rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED

Resume eval_no_mutation_scopes[RawCall]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def, option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED

Resume eval_no_mutation_scopes[RawCallCalldata]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, type_check_def, assert_def, lift_option_type_def, option_CASE_rator] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac eval_raw_call_preserves_non_accounts >> gvs[] >> metis_tac[]
QED

Resume eval_no_mutation_scopes[RawLog]:
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
       raise_def, check_def, type_check_def, assert_def, lift_option_def,
       lift_option_type_def, push_log_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >> metis_tac[]
QED

Resume eval_no_mutation_scopes[RawRevert]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def,
      raise_def, check_def, type_check_def, assert_def] >> metis_tac[]
QED

Finalise eval_no_mutation_scopes

Theorem eval_expr_no_mutation_scopes:
  !ce cx e st res st'. ~expr_can_mutate ce e /\
    eval_expr cx e st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[eval_no_mutation_scopes]
QED

Theorem eval_exprs_no_mutation_scopes:
  !ce cx es st res st'. ~exprs_can_mutate ce es /\
    eval_exprs cx es st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[eval_no_mutation_scopes]
QED

Theorem eval_expr_results_no_mutation_scopes:
  !ce cx es st res st'. ~exprs_can_mutate ce es /\
    eval_expr_results cx es st = (res,st') ==> st'.scopes = st.scopes
Proof
  metis_tac[eval_no_mutation_scopes]
QED
