(* Source-specific full composition retains the same endpoint for every horizon.
   Only the left outcome and the semantic continuation remain for consumers. *)
Theory augAssignFullBindStages
Ancestors
  gasOutcomeFullCompose gasExemptCert stmtSimAugAssignPlaceMemory
  stmtSimAugAssign vyperStorageTrace vyperState vyperInterpreter

Theorem augassign_target_bind_full:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (eval_target_place cx target) (es, s, G, tn)
    Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. eval_target_place cx target
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Q1 H res mid G1 tn1 t) ==>
     (?p. res = INL p /\
       gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
         (bind (read_place cx p) (\cur.
           bind (place_type_value cx p) (\ptv.
             bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
               bind (lift_sum (evaluate_binop
                 (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                 ptv bop cur rhs)) (write_place cx p)))))
         (mid, t, G1, tn1) Q R) \/
     (?exc. res = INR exc /\
       !H. valid_horizon cx st0 H mid.storage_trace ==>
           Q H (INR exc) mid G1 tn1 t)) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (bind (eval_target_place cx target) (\p.
      bind (read_place cx p) (\cur.
        bind (place_type_value cx p) (\ptv.
          bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
            bind (lift_sum (evaluate_binop
              (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
              ptv bop cur rhs)) (write_place cx p))))))
    (es, s, G, tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_bind_all >> BETA_TAC >>
  conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_place] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_place_type] >> gen_tac >>
      irule storage_trace_frame_bind_all >>
      simp[augassign_rhs_trace_frame, aug_place_store_trace_frame]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_place >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_place >> simp[]) >>
  conj_tac >- simp[cj 8 evaluate_storage_trace_frame] >>
  qexists_tac `Q1` >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED

Theorem augassign_rhs_bind_full:
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es, s, G, tn)
    Q1 (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
        (res, mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
          Q1 H res mid G1 tn1 t) ==>
     (?rhs. res = INL rhs /\
       gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
         (bind (lift_sum (evaluate_binop
           (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
           ptv bop cur rhs)) (write_place cx p))
         (mid, t, G1, tn1) Q R) \/
     (?exc. res = INR exc /\
       !H. valid_horizon cx st0 H mid.storage_trace ==>
           Q H (INR exc) mid G1 tn1 t)) ==>
  gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
    (bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
        ptv bop cur rhs)) (write_place cx p)))
    (es, s, G, tn) Q R
Proof
  strip_tac >> irule gas_outcome_full_bind_all >> BETA_TAC >>
  conj_tac >- simp[aug_place_store_trace_frame] >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[augassign_rhs_trace_frame] >>
  qexists_tac `Q1` >> conj_tac >- first_assum ACCEPT_TAC >>
  first_assum ACCEPT_TAC
QED
