(* Request-prefix companion to augAssignFullBindStages. *)
Theory s1PrefixAugAssignBindStages
Ancestors
  s1PrefixPreds augAssignFullBindStages s1PrefixDefs s1PrefixCompose s1PrefixProps
  stmtSimAugAssign stmtSimAugAssignPlaceMemory vyperStorageBackend vyperState list sum

Theorem augassign_target_bind_prefix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (eval_target_place cx target) (es,s,G,tn)
    Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_target_place cx target) (es,s,G,tn) /\
  (!marks p mid G1 tn1 t.
     (!tail. eval_target_place cx target
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (INL p,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==> Q1 H (INL p) mid G1 tn1 t) ==>
     gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
       (bind (read_place cx p) (\cur.
         bind (place_type_value cx p) (\ptv.
           bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
             bind (lift_sum (evaluate_binop
               (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
               ptv bop cur rhs)) (write_place cx p)))))
       (mid,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (eval_target_place cx target) (\p.
      bind (read_place cx p) (\cur.
        bind (place_type_value cx p) (\ptv.
          bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
            bind (lift_sum (evaluate_binop
              (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
              ptv bop cur rhs)) (write_place cx p))))))
    (es,s,G,tn)
Proof
  cheat
QED

Theorem augassign_rhs_bind_prefix:
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) /\
  (!H v mid G1 tn1 t. Q1 H (INL v) mid G1 tn1 t ==> ~t.vs_halted) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p)))
    (es,s,G,tn)
Proof
  strip_tac >>
  drule_then irule gas_prefix_full_bind_no_outcome >>
  simp[augassign_rhs_trace_frame, aug_place_store_trace_frame,
       requests_outcomes_frame_bind_all, requests_outcomes_frame_read_result,
       evaluate_requests_outcomes_frame] >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.ISR]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >>
  reverse (Cases_on `evaluate_binop (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                                    ptv bop cur v`) >>
  simp[bind_def, lift_sum_def, return_def, raise_def]
  >- (rpt strip_tac >> gvs[]) >>
  Cases_on `p`
  >- (rename1 `write_place _ (StoragePlace tr _ _) _ _ = _ ==> _` >>
      Cases_on `tr` >>
      simp[write_place_def, write_storage_slot_eq, set_storage_def] >>
      rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[write_place_def, bind_def, ignore_bind_def, get_scopes_def,
       set_scopes_def, lift_option_type_def, lift_sum_def, type_check_def,
       assert_def, return_def, raise_def, get_immutables_def,
       set_immutable_def, get_address_immutables_def, set_address_immutables_def,
       vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  qpat_assum `find_containing_scope _ _ = SOME _` mp_tac >>
  rename1 `find_containing_scope _ _ = SOME parts` >> PairCases_on `parts` >>
  gvs[bind_def, ignore_bind_def, set_scopes_def, lift_sum_def, assert_def,
      return_def, raise_def, vyperMiscTheory.sum_CASE_rator, AllCaseEqs()]
QED
