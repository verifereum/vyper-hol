Theory entryCreateNameLoad
Ancestors
  entryCreateFocusSpec entryCreatePathScope entryCreatePendingScope entryCreateCompletedCut
  bodyFullNameWord exprSimFullBundleProps s1PrefixDefs
  gasOutcomeFull fragGasOriginPtr fragGasOrigin gasStorage gasSummary
  createSizePrefixReplay createMarkedPath abiEncoderProps
  vyperStorageFootprint vyperStorageTrace relation

Theorem create_name_load_scope[local]:
  ~(s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_id IN frag_ids a b /\
  gas_origin_edge F E C fn s [] (OK t) /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts ==>
  create_operand_full_scope a b E C fn s [] (OK t)
Proof
  strip_tac >> simp[create_operand_full_scope_def, create_expr_prefix_marked] >>
  irule RTC_SINGLE >> simp[create_marked_edge_def,create_prefix_step_def] >>
  metis_tac[]
QED

Theorem name_load_edge_plain[local]:
  gas_origin_ptr_edge (D,lo,E,C,fn,PG) (s,G,tn) [] (OK t,G',tn') ==>
  gas_origin_edge F E C fn s [] (OK t)
Proof
  simp[gas_origin_ptr_edge_def,gas_origin_edge_def] >> metis_tac[]
QED

Theorem create_name_word_scoped:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann ==>
  expr_sim_scoped (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Name ann id) es
Proof
  rw[expr_sim_scoped_def] >>
  `~s0.vs_halted` by fs[expr_sim_full_pre_def] >>
  qabbrev_tac `source = vyperState$bind (eval_expr cx (Name ann id)) (read_result cx)` >>
  rewrite_tac[scoped_operand_outcome_def] >> qexists_tac `[]` >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- (`expr_sim_full_hypotheses (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty (Name ann id) es (st0,sa,sb,sha,shb,op,s0,G0,tn0)` by
        (qpat_assum `expr_sim_full_pre _ _ _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[expr_sim_full_pre_def,expr_sim_full_hypotheses_def,
                          expr_sim_full_code_def, CONJ_ASSOC] >>
         disch_then ACCEPT_TAC) >>
      drule_all name_word_full_edge >> strip_tac >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`INL v`,`es`,`OK t`,`G`,`tn`] >>
      conj_tac
      >- (`valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
            fs[storage_trace_domain_def] >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
          drule_then assume_tac name_load_edge_plain >>
          irule create_name_load_scope >> simp[frag_ids_def] >> metis_tac[]) >>
      simp[Abbr `source`,gas_explicit_def] >> gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
      `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (t,G,tn) [] (OK t,G,tn)` by simp[gas_origin_ptr_path_rules] >>
      drule_all (cj 2 gas_origin_ptr_path_rules) >> simp[]) >>
  disj1_tac >>
  conj_tac
  >- (simp[gas_bad_storage_at_def,gas_explicit_def] >> gen_tac >>
      `storage_trace_frame source` by
        simp[Abbr `source`,storage_trace_frame_bind,evaluate_storage_trace_frame,
             storage_trace_frame_read_result] >>
      Cases_on `source (es with gas_obs := tail)` >> simp[] >>
      `~storage_trace_domain cx st0 (es with gas_obs := tail).storage_trace` by simp[] >>
      drule_all storage_trace_frame_preserves_bad_domain >> simp[]) >>
  conj_tac >- (irule create_operand_focus_scope_caller >> qexists_tac `s0` >> simp[]) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,`G0`,`tn0`,`s0`] >>
  simp[gas_origin_ptr_focus_nil]
QED
