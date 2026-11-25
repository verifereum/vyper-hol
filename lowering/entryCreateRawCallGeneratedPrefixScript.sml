(* Source-neutral lowered prefixes may consume generated GAS readings. *)
Theory entryCreateRawCallGeneratedPrefix
Ancestors
  bodyFullRawCallGeneratedPrefix entryCreateCompletedCut entryCreatePathScope
  entryCreatePendingScope createSizePrefixReplay createSizeCutRegion createSizeCutCode
  bodyDeclMemoryCompose fragGasOriginPtr fragGasOrigin fragGasPathMem fragGasMode
  gasStorage gasExemptCert gasSummary gasSummaryCompose vyperStorageTrace
  vyperStorageFootprint vyperInterpreter vyperState venomState list

Theorem raw_call_generated_prefix_scoped:
  storage_trace_frame source /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) (REPLICATE n F) (OK t,G1,tn1)) /\
  create_operand_full_scope i j E C f s (REPLICATE n F) (OK t) /\
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
  `create_expr_prefix i j E C f s (REPLICATE n F) t` by
    fs[create_operand_full_scope_def] >>
  `!marks. create_operand_focus_scope j z E C f t marks ==>
           create_operand_focus_scope i z E C f s (REPLICATE n F ++ marks)` by
    (rpt strip_tac >> irule create_operand_focus_scope_join >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- metis_tac[] >> qexistsl_tac [`j`,`t`] >> simp[]) >>
  `!marks r. create_operand_full_scope j z E C f t marks r ==>
             create_operand_full_scope i z E C f s (REPLICATE n F ++ marks) r` by
    (rpt strip_tac >> irule create_operand_full_scope_prepend >>
     qexistsl_tac [`j`,`t`] >> simp[]) >>
  `gas_path_mem C f s n (OK t)` by
    (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
        es.storage_trace` by fs[storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     drule gas_origin_ptr_path_projections >> strip_tac >>
     drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `!marks. gas_explicit (REPLICATE n F ++ marks) s.vs_gas_readings =
           gas_explicit marks t.vs_gas_readings` by
    (drule gas_path_mem_ok_suffix >> simp[gas_explicit_append]) >>
  `!H focus endpt.
     (storage_trace_domain cx st0 es.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace) /\
     gas_origin_ptr_focus (DF H,lo,E,C,f,PG) (t,G1,tn1) focus endpt ==>
     gas_origin_ptr_focus (DF H,lo,E,C,f,PG) (s,G,tn)
       (REPLICATE n F ++ focus) endpt` by
    (rpt strip_tac >> PairCases_on `endpt` >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- metis_tac[] >> strip_tac >>
     drule (cj 2 gas_origin_ptr_focus_rules) >> disch_then drule >> simp[]) >>
  qpat_x_assum `scoped_operand_outcome _ _ _ _ j z _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [scoped_operand_outcome_def]) >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `REPLICATE n F ++ marks`
  >- (disj1_tac >> conj_tac >- gvs[gas_bad_storage_at_def] >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >> simp[] >>
      metis_tac[])
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
      conj_tac >- metis_tac[] >> simp[] >> rpt strip_tac >>
      `valid_horizon cx st0 H es.storage_trace` by
        (qpat_assum `!tail. source _ = _` (qspec_then `[]` assume_tac) >>
         `valid_horizon cx st0 H (ee with gas_obs := []).storage_trace` by simp[] >>
         drule_all valid_horizon_frame >> simp[]) >>
      res_tac >> metis_tac[gas_origin_ptr_path_append]) >>
  disj2_tac >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (irule raw_call_exempt_generated_prefix >> qexists_tac `t` >> simp[]) >>
  qexists_tac `H` >> simp[] >> metis_tac[]
QED
