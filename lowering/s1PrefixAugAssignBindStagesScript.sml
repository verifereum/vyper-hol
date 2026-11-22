(* Request-prefix companion to augAssignFullBindStages. *)
Theory s1PrefixAugAssignBindStages
Ancestors
  s1PrefixPreds augAssignFullBindStages s1PrefixDefs
  s1PrefixCompose s1PrefixProps vyperStorageTrace
  stmtSimAugAssign stmtSimAugAssignPlaceMemory

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
  strip_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind) >>
  BETA_TAC >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac >- (rpt strip_tac >> simp[]) >>
  gen_tac >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_read_place] >> gen_tac >>
  irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_place_type] >> gen_tac >>
  irule storage_trace_frame_bind_all >>
  simp[augassign_rhs_trace_frame, aug_place_store_trace_frame]
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
  cheat
QED
