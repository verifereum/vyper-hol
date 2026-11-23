Theory linkedDefaultEvaluation
Ancestors
  linkedDefaultOutcomeBind linkedDefaultOutcomeSource gasOutcomeFullModsSource gasExemptCertMods exprSimWordArgs vyperInterpreter vyperStorageFootprint vyperStorageTrace vyperState sum pair list

Theorem grouped_default_exprs_cons_outcome_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res ee G' tn' t. ?v. res = INL v /\ P H v ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r) /\
  (!marks v mid G1 tn1 t.
     (!tail. bind (eval_expr cx e) (read_result cx)
       (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
       (INL v,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       P H v mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,explicit,ctx,fn,PG)
         (s,G,tn) marks (OK t,G1,tn1)) ==>
     gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
       (eval_exprs cx xs) (mid,t,G1,tn1)
       (\H res ee G' tn' u. ?vs. res = INL vs /\ Q H (v::vs) ee G' tn' u)
       (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0
    (eval_exprs cx (e::xs)) (es,s,G,tn)
    (\H res ee G' tn' t. ?vs. res = INL vs /\ Q H vs ee G' tn' t)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)
Proof
  strip_tac >> rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all_path_mods >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
          storage_trace_frame_return] >>
  qexists_tac `\H res ee G' tn' t. ?v. res = INL v /\ P H v ee G' tn' t` >>
  conj_tac
  >~ [`gas_origin_ptr_path _ _ _ _`]
  >- suspend "tail" >>
  BETA_TAC >> irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_expr _ _) _) _ _ _`
    (irule_at Any) >> simp[] >> metis_tac[sumTheory.INR_11]
QED

Resume grouped_default_exprs_cons_outcome_mods[tail]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?v. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `v` >> simp[] >>
  `gas_outcome_full_mods (DF,lo,explicit,ctx,fn,PG) mods cx st0 (eval_exprs cx xs)
    (mid,t,G1,tn1)
    (\H res ee G' tn' u. ?vs. res = INL vs /\ Q H (v::vs) ee G' tn' u)
    (\H res ee gt r. ?ex. res = INR ex /\ R H ex ee gt r)` by
    (first_x_assum (qspecl_then [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] irule) >>
     asm_rewrite_tac[] >> simp[] >> metis_tac[sumTheory.INL_11]) >>
  `!src. bind (eval_exprs cx xs) (\vs. return (v::vs)) src =
     (sum$SUM_MAP (CONS v) I (FST (eval_exprs cx xs src)),
      SND (eval_exprs cx xs src))` by
    (gen_tac >> Cases_on `eval_exprs cx xs src` >>
     rename1 `eval_exprs cx xs src = (rs,ee)` >>
     Cases_on `rs` >> simp[bind_def, return_def, sumTheory.SUM_MAP_def]) >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (eval_exprs cx xs) _ _ _`
    (mp_then (Pos last)
       (mp_tac o BETA_RULE o Q.ISPECL
         [`bind (eval_exprs cx xs) (\vs. return ((v:value)::vs))`,
          `sum$SUM_MAP (CONS (v:value)) (I : exception -> exception)`])
       gas_outcome_full_source_map_mods) >>
  impl_tac >- simp[sumTheory.SUM_MAP_def] >>
  disch_tac >> irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ (bind (eval_exprs cx xs) _) _ _ _`
    (irule_at Any) >>
  simp[PULL_EXISTS, sumTheory.SUM_MAP_def] >>
  metis_tac[]
QED

Finalise grouped_default_exprs_cons_outcome_mods
