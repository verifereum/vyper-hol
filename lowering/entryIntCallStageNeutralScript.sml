(* Scoped counterparts of the neutral actions in internal-call staging. *)
Theory entryIntCallStageNeutral
Ancestors
  entryCreateCompletedCut entryCreatePathScope entryCreatePendingScope
  createSizePrefixReplay createSizeCutRegion createSizeCutCode
  exprSimMemorySource gasOutcomeFull bodyDeclMemoryCompose
  fragGasOriginPtr fragGasOrigin fragGasPathMem fragGasMode fragExec
  gasStorage gasExemptCert gasSummary vyperStorageTrace vyperStorageFootprint
  vyperInterpreter vyperState venomState relation list

Theorem stage_scoped_initial_domain:
  storage_trace_frame source /\ ~s.vs_halted /\
  (storage_trace_domain cx st0 es.storage_trace ==>
   scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 i z
     source (es,s,G,tn) Q R) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 i z
    source (es,s,G,tn) Q R
Proof
  strip_tac >> Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- metis_tac[] >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  conj_tac >- (irule gas_bad_storage_at_initial >> simp[]) >>
  conj_tac
  >- (irule create_operand_focus_scope_caller >> qexists_tac `s` >>
      simp[create_expr_prefix_marked]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`f`,`PG`,`G`,`tn`,`s`] >>
  simp[gas_origin_ptr_focus_nil]
QED

(* Successful unchanged-state reads are neutral on the entire gas orbit.
   In particular neither a frame premise nor a new target step is needed. *)
Theorem stage_scoped_read_result:
  read_result cx tv es = (INL v,es) /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 i z (k v)
    (es with gas_obs := [],s,G,tn) Q R ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 i z
    (bind (read_result cx tv) k) (es,s,G,tn) Q R
Proof
  strip_tac >> drule read_result_gas_obs >> strip_tac >>
  `!gs. bind (read_result cx tv) k (es with gas_obs := gs) =
        k v (es with gas_obs := gs)` by simp[bind_def] >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac >- fs[gas_bad_storage_at_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> fs[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> fs[]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (irule gas_exempt_cert_source_cong >>
      qexists_tac `ignore_bind (k v) (return ())` >> conj_tac
      >- simp[ignore_bind_def, bind_def] >>
      drule gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  qexists_tac `H` >> fs[]
QED

(* Unlike an empty scope, a zero-mark prefix can execute real instructions. *)
Theorem stage_scoped_zero_prefix:
  storage_trace_frame source /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK t,G1,tn1)) /\
  create_operand_full_scope i j E C f s [] (OK t) /\
  i.cs_next_id <= j.cs_next_id /\ j.cs_next_id <= z.cs_next_id /\
  (!bb inst. lookup_block z.cs_current_bb f.fn_blocks = SOME bb /\
      get_instruction bb (LENGTH z.cs_current_insts) = SOME inst ==>
      inst.inst_id NOTIN frag_ids i j) /\
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} j z /\ fn_has_code j z f /\ create_cut_region j z t /\
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 j z
    source (es,t,G1,tn1) Q R ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 i z
    source (es,s,G,tn) Q R
Proof
  strip_tac >>
  `create_expr_prefix i j E C f s [] t` by fs[create_operand_full_scope_def] >>
  `!marks. create_operand_focus_scope j z E C f t marks ==>
           create_operand_focus_scope i z E C f s marks` by
    (rpt strip_tac >> irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`first` |-> `[]`] create_operand_focus_scope_join)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- metis_tac[] >> qexistsl_tac [`j`,`t`] >> simp[]) >>
  `!marks r. create_operand_full_scope j z E C f t marks r ==>
             create_operand_full_scope i z E C f s marks r` by
    (rpt strip_tac >> irule (SIMP_RULE (srw_ss()) []
       (Q.INST [`left` |-> `[]`] create_operand_full_scope_prepend)) >>
     qexistsl_tac [`j`,`t`] >> simp[]) >>
  `gas_path_mem C f s 0 (OK t)` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
       fs[storage_trace_domain_def] >>
     res_tac >> drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `t.vs_gas_readings = s.vs_gas_readings` by (drule gas_path_mem_ok_suffix >> simp[]) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ j z _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `marks`
  >- (disj1_tac >> conj_tac
      >- (rewrite_tac[gas_bad_storage_at_def] >>
          qpat_assum `t.vs_gas_readings = s.vs_gas_readings`
            (once_rewrite_tac o single o SYM) >> fs[gas_bad_storage_at_def]) >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[] >>
      metis_tac[cj 2 gas_origin_ptr_focus_rules, APPEND])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- metis_tac[] >> conj_tac
      >- (qpat_assum `t.vs_gas_readings = s.vs_gas_readings`
            (once_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
         `valid_horizon cx st0 H (ee with gas_obs := []).storage_trace` by simp[] >>
         drule_all valid_horizon_frame >> simp[]) >>
      res_tac >> simp[] >>
      metis_tac[gas_origin_ptr_path_append, APPEND]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[gas_exempt_cert_zero_prefix_mem] >>
  qexists_tac `H` >> simp[] >>
  metis_tac[cj 2 gas_origin_ptr_focus_rules, APPEND]
QED
