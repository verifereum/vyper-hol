(* Scope the bytecode operand on its chosen VV return. A normal return
   supplies the source read and the input to the physical preparation. *)
Theory entryCreateRawBytecodeBind
Ancestors
  entryCreateFocusSpec entryCreateCompositeFocus entryIntCallStageNeutral
  exprSimAggregateSource exprSimMemorySource gasStorage vyperStorageFootprint
  vyperInterpreter vyperState gasExemptCert vyperStorageTrace stmtSimProps
  entryCreateCompletedCut exprSimDefs s1PrefixDefs fragExec

Theorem raw_create_scoped_bytecode_read[local]:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!tail. eval_expr cx code (es with gas_obs := gs ++ tail) =
    (res,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_vv_post (DF,lo,d,ctx,func) ce cx code
      (es,sa,a,s,vv,G,tn) H res ee G1 tn1 t) ==>
  ?raw v. res = INL raw /\ read_result cx raw ee = (INL v,ee) /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gs ++ tail) = (INL v,ee with gas_obs := tail))
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (drule_then (strip_assume_tac o REWRITE_RULE [create_operand_vv_post_def])) >>
  drule vv_post_materialises >> strip_tac >>
  qexistsl_tac [`tv`,`v`] >> simp[Once bind_def] >>
  metis_tac[read_result_gas_obs]
QED

(* Record the continuation at the chosen normal return, before forgetting
   the scope and all-horizon path in the generic cross-type bind. *)
Theorem raw_create_vv_record_next[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa a
    (eval_expr cx code) (es,s,G,tn) P (create_operand_exit_post C cx) /\
  (!marks res ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\
    create_operand_full_scope sa a E C f s marks (OK t) /\
    (!tail. eval_expr cx code (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (res,ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      P H res ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    ?raw. res = INL raw /\ next_ready raw ee G1 tn1 t) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 sa a
    (eval_expr cx code) (es,s,G,tn)
    (\H res ee G1 tn1 t. ?raw. res = INL raw /\ next_ready raw ee G1 tn1 t)
    (\H res ee gt r. ?exc. res = INR exc /\
      create_operand_exit_post C cx H (INR exc : value + exception) ee gt r)
Proof
  simp[scoped_operand_outcome_def] >> disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac) >>
  qexists_tac `marks`
  >- (disj1_tac >> metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
      Cases_on `exit_result r`
      >- (rpt strip_tac >> res_tac >> fs[exit_result_def] >> Cases_on `res` >>
           fs[create_operand_exit_post_def,expr_exit_def,halt_exit_def,expr_exit_INR_type]) >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
        by fs[storage_trace_domain_def] >>
      `?t. r = OK t` by metis_tac[] >> gvs[exit_result_def] >>
      qpat_assum `!marks res ee G1 tn1 t. _ ==> _`
        (qspecl_then [`marks`,`res`,`ee with gas_obs := []`,`G'`,`tn'`,`t`] mp_tac) >>
      (impl_tac >- (simp[] >> rpt strip_tac >> res_tac >> fs[])) >>
      rpt strip_tac >> res_tac >> simp[]) >>
  disj2_tac >> disj2_tac >> metis_tac[]
QED

Theorem raw_create_bytecode_scoped_bind_of_handoff:
  expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type code) code es
    (st0,sa,a,sha,shb,vv,s,G,tn) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre ce cx env code es /\
  (body_const_cells_agree [(NONE,tops)] cx env es /\ expr_body_pre ce cx env code es ==>
    expr_vv_sim_scoped (DF,lo,d,C,shC,PG,f,shf) ce cx (expr_type code) code es) /\
  (!marks raw v ee G1 tn1 t.
    storage_trace_domain cx st0 ee.storage_trace /\ create_operand_at a t /\
    create_operand_full_scope sa a (gas_explicit_sites C shC) C f s marks (OK t) /\
    (!tail. eval_expr cx code (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL raw,ee with gas_obs := tail)) /\
    read_result cx raw ee = (INL v,ee) /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL v,ee with gas_obs := tail)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      create_operand_vv_post (DF,lo,d,C,f) ce cx code (es,sa,a,s,vv,G,tn)
        H (INL raw) ee G1 tn1 t /\
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)) ==>
    ?bs z Gz tz. v = BytesV bs /\ window marks bs ee z Gz tz /\
      create_operand_full_scope a b (gas_explicit_sites C shC) C f t [] (OK z) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG) (t,G1,tn1) [] (OK z,Gz,tz))) /\
  (!marks bs ee z Gz tz.
    window marks bs ee z Gz tz /\
    (!tail. bind (eval_expr cx code) (read_result cx)
      (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
      (INL (BytesV bs),ee with gas_obs := tail)) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st0 b c
      (next (BytesV bs)) (ee,z,Gz,tz) Q (create_operand_exit_post C cx)) /\
  (!v. storage_trace_frame (next v)) /\
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  (!bb inst. lookup_block c.cs_current_bb f.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH c.cs_current_insts) = SOME inst ==>
    inst.inst_id NOTIN frag_ids a b) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\ create_cut_code {} b c /\ fn_has_code b c f /\
  (!z. create_operand_at b z ==> create_cut_region b c z) /\
  (!marks. create_operand_focus_scope sa a (gas_explicit_sites C shC) C f s marks ==>
    create_operand_focus_scope sa c (gas_explicit_sites C shC) C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope sa a (gas_explicit_sites C shC) C f s marks r ==>
    create_operand_full_scope sa c (gas_explicit_sites C shC) C f s marks r) /\
  (!left t right. create_operand_full_scope sa a (gas_explicit_sites C shC) C f s left (OK t) /\
    create_operand_focus_scope a c (gas_explicit_sites C shC) C f t right ==>
    create_operand_focus_scope sa c (gas_explicit_sites C shC) C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope sa a (gas_explicit_sites C shC) C f s left (OK t) /\
    create_operand_full_scope a c (gas_explicit_sites C shC) C f t right r ==>
    create_operand_full_scope sa c (gas_explicit_sites C shC) C f s (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st0 sa c
    (bind (bind (eval_expr cx code) (read_result cx)) next) (es,s,G,tn) Q
    (create_operand_exit_post C cx)
Proof
  strip_tac >> fs[expr_vv_sim_scoped_def] >> res_tac >>
  rewrite_tac[bind_assoc] >> irule scoped_operand_bind >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_bind_all,storage_trace_frame_read_result] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      drule_then irule gas_exempt_cert_bind_result >> fs[ignore_bind_def,bind_assoc])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> simp[ignore_bind_def,bind_assoc] >>
      irule gas_exempt_cert_error_result >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `ready = \raw ee G1 tn1 t.
    scoped_operand_outcome (DF,lo,gas_explicit_sites C shC,C,f,PG) (cx_tops cx) cx st0 a c
      (bind (read_result cx raw) next) (ee,t,G1,tn1) Q (create_operand_exit_post C cx)` >>
  qexistsl_tac [`\H raw ee G1 tn1 t. ready raw ee G1 tn1 t`, `a`] >>
  asm_rewrite_tac[] >> BETA_TAC >> reverse conj_tac
  >- (qpat_assum `scoped_operand_outcome _ _ _ _ sa a _ _ _ (create_operand_exit_post C cx)`
        (mp_then Any mp_tac raw_create_vv_record_next) >>
      disch_then (qspec_then `ready` mp_tac) >> BETA_TAC >>
      (impl_tac >- (simp[Abbr `ready`] >> rpt strip_tac >>
        `create_operand_at a t` by (fs[create_operand_full_scope_def,create_operand_at_def]) >>
        `!H. valid_horizon cx st0 H ee.storage_trace ==>
          create_operand_vv_post (DF,lo,d,C,f) ce cx code (es,sa,a,s,vv,G,tn)
            H res ee G1 tn1 t /\
          gas_origin_ptr_path (DF H,lo,gas_explicit_sites C shC,C,f,PG) (s,G,tn) marks (OK t,G1,tn1)`
          by (rpt strip_tac >> res_tac) >>
        `!H. valid_horizon cx st0 H ee.storage_trace ==>
          create_operand_vv_post (DF,lo,d,C,f) ce cx code (es,sa,a,s,vv,G,tn)
            H res ee G1 tn1 t` by (rpt strip_tac >> res_tac) >>
        drule_all raw_create_scoped_bytecode_read >> strip_tac >>
        qpat_x_assum `res = INL raw` SUBST_ALL_TAC >>
        qpat_assum `!ms rv x ee g n t. _ ==> ?bs z Gz tz. x = BytesV bs /\ _`
          (qspecl_then [`marks`,`raw`,`v`,`ee`,`G1`,`tn1`,`t`] mp_tac) >>
        (impl_tac >- simp[]) >> strip_tac >>
        qexists_tac `raw` >> simp[] >> irule stage_scoped_read_result >>
        qexists_tac `BytesV bs` >> simp[] >>
        `ee with gas_obs := [] = ee` by (Cases_on `ee` >> fs[]) >>
        asm_rewrite_tac[] >> irule stage_scoped_zero_prefix >>
        FAIL_TAC "physical prefix")) >>
      disch_then ACCEPT_TAC) >>
  rpt strip_tac >> `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace`
    by fs[storage_trace_domain_def] >> metis_tac[]
QED
