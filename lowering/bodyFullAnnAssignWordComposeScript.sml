(* Word declaration sequencing exposes normality of the selected RHS endpoint. *)
Theory bodyFullAnnAssignWordCompose
Ancestors
  bodyFullAnnAssignCompose gasOutcomeFull fragGasOriginPtr fragGasSeqPtr
  vyperStorageTrace vyperStorageFootprint vyperState vyperInterpreter list

Theorem annassign_word_full_outcome:
  !DF lo explicit ctx func PG tops cx st0 id typ tyv e es s G tn Q R P S lctx.
    evaluate_type (get_tenv cx) typ = SOME tyv /\
    gas_admissible (eval_stmt cx (AnnAssign id typ e)) (stmt_res_ok lctx) es /\
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es, s, G, tn) Q R /\
    (!H res ee G1 tn1 t. Q H res ee G1 tn1 t ==> ?v. res = INL v) /\
    (!H res ee gt r. R H res ee gt r ==>
       ?exc. res = INR exc /\ S H (INR exc) ee gt r) /\
    (!marks v mid G1 tn1 t.
       (!tail. bind (eval_expr cx e) (read_result cx)
           (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
           (INL v, mid with gas_obs := tail)) /\
       storage_trace_domain cx st0 mid.storage_trace /\
       ~t.vs_halted /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
            Q H (INL v) mid G1 tn1 t) ==>
       ?ff u G2 tn2.
         (!tail. new_variable id tyv v (mid with gas_obs := tail) =
                 (INL (), ff with gas_obs := tail)) /\
         ff.storage_trace = mid.storage_trace /\
         (!H. valid_horizon cx st0 H ff.storage_trace ==>
            gas_origin_ptr_path (DF H, lo, explicit, ctx, func, PG)
              (t, G1, tn1) [] (OK u, G2, tn2) /\
            P H (INL ()) (ff with gas_obs := []) G2 tn2 u)) ==>
    gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (eval_stmt cx (AnnAssign id typ e)) (es, s, G, tn) P S
Proof
  rpt gen_tac >> strip_tac >>
  `gas_outcome_full (DF, lo, explicit, ctx, func, PG) tops cx st0
      (bind (eval_expr cx e) (read_result cx)) (es, s, G, tn)
      (\H res ee G1 tn1 t. Q H res ee G1 tn1 t /\ ~t.vs_halted) R` by
    (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rw[gas_outcome_full_def] >> qexists_tac `marks`
     >- metis_tac[]
     >- (disj2_tac >> disj1_tac >>
         qexistsl_tac [`res`, `ee`, `r`, `G'`, `tn'`] >> simp[] >>
         rpt strip_tac >> first_x_assum drule >> strip_tac >>
         metis_tac[gas_origin_ptr_path_projections, gas_path_ptr_ok_not_halted]) >>
     metis_tac[]) >>
  irule annassign_full_outcome >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`(\H res ee G1 tn1 t. Q H res ee G1 tn1 t /\ ~t.vs_halted)`, `R`, `tyv`] >>
  simp[] >> reverse conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >>
  `~t.vs_halted` by metis_tac[] >>
  qpat_x_assum `!marks v mid G1 tn1 t. _` irule >>
  (metis_tac[])
QED
