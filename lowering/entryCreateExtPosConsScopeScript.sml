Theory entryCreateExtPosConsScope
Ancestors
  entryCreateScopedBind entryCreateCompletedCut entryCreateFocusSpec
  exprSimWordArgs exprSimDefs stmtSimProps fragGasOriginPtr fragGasOrigin fragGasMode
  fragExec gasExemptCert gasStorage vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState

Theorem pos_cons_head_normalized[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P
    (create_operand_exit_post C cx) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    (\H res mid G1 tn1 t. mid.gas_obs = [] /\ P H res mid G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post C cx H (INR exc : value list + exception) ee gt r)
Proof
  rewrite_tac[scoped_operand_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      simp[] >>
      Cases_on `res` >> fs[create_operand_exit_post_def,halt_exit_def] >>
      metis_tac[expr_exit_INR_type]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem pos_cons_scope_mixed:
  (!marks. create_operand_focus_scope a m E C f s marks ==>
     create_operand_focus_scope a b E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
     create_operand_full_scope a b E C f s marks r) /\
  (!left t right.
     create_operand_full_scope a m E C f s left (OK t) /\
     create_operand_focus_scope m b E C f t right ==>
     create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r.
     create_operand_full_scope a m E C f s left (OK t) /\
     create_operand_full_scope m b E C f t right r ==>
     create_operand_full_scope a b E C f s (left ++ right) r) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m
    (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) P (create_operand_exit_post C cx) /\
  (!H r ee G1 tn1 t. P H r ee G1 tn1 t ==> ?v. r = INL v) /\
  (!obs marks v mid G1 tn1 t.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := obs) =
      (INL v,mid with gas_obs := []) /\
    (?H. valid_horizon cx st0 H mid.storage_trace) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      P H (INL v) (mid with gas_obs := []) G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 m b
      (bind (eval_exprs cx xs) (\vs. return (v::vs))) (mid with gas_obs := [],t,G1,tn1) Q
      (create_operand_exit_post C cx)) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
    (eval_exprs cx (e::xs)) (es,s,G,tn) Q (create_operand_exit_post C cx)
Proof
  strip_tac >> drule_then assume_tac pos_cons_head_normalized >>
  pure_rewrite_tac[eval_exprs_cons_action] >> irule scoped_operand_bind_all_mixed >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_read_result,
       storage_trace_frame_return,storage_trace_frame_bind_all] >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
      pure_once_rewrite_tac[bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_value >> simp[GSYM ignore_bind_def]) >>
  conj_tac
  >- (rpt strip_tac >> pure_rewrite_tac[ignore_bind_def] >>
      pure_once_rewrite_tac[bind_assoc] >>
      irule gas_exempt_cert_error_value >> simp[]) >>
  qexistsl_tac [`\H res mid G1 tn1 t. mid.gas_obs = [] /\ P H res mid G1 tn1 t`,`m`] >>
  simp[] >> rpt conj_tac
  >- (map_every qx_gen_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
      `?H. valid_horizon cx st0 H mid.storage_trace` by metis_tac[storage_trace_domain_def] >>
      `mid.gas_obs = [] /\ ?v. res = INL v` by metis_tac[] >> gvs[] >>
      `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
      qpat_assum `mid with gas_obs := [] = mid` (SUBST1_TAC o SYM) >>
      qpat_assum `!obs marks v mid G1 tn1 t. _` irule >>
      conj_tac >- (qexists_tac `marks` >> simp[]) >>
      conj_tac >- metis_tac[] >>
      qexists_tac `gas_explicit marks s.vs_gas_readings` >>
      qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
      qpat_assum `mid with gas_obs := [] = mid`
        (fn th => rewrite_tac[listTheory.APPEND_NIL, th])) >>
  metis_tac[]
QED
