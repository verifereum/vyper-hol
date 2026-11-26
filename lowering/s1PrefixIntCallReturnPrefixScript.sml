(* Transport the callee request sites through INVOKE and source cleanup. *)
Theory s1PrefixIntCallReturnPrefix
Ancestors
  s1PrefixDefs bodyFullIntCallReturnSource bodyFullIntCallDefs
  bodyIntCallSeams fragGasFocus fragGasOriginPtr vyperState vyperInterpreter
  vyperTypeEvalStoragePreservation

Theorem intcall_rest_trace_suffix[local]:
  !cx name mut nr ss prev rtv st.
    ?suffix. (!rq outcome. ~MEM (StorageOutcome rq outcome) suffix) /\
      (SND (intcall_rest cx name mut nr ss prev rtv st)).storage_trace =
      (SND (intcall_callee_src cx name mut nr ss st)).storage_trace ++ suffix
Proof
  rpt gen_tac >>
  Cases_on `lock_if_nr cx nr (is_view_mut mut) st` >>
  rename1 `_ = (lock_res,locked)` >> Cases_on `lock_res`
  >- (asm_simp_tac bool_ss [intcall_rest_def,intcall_callee_src_def,ignore_bind_def,
        bind_def,pairTheory.pair_case_thm,sumTheory.sum_case_def,pairTheory.SND] >>
      Cases_on `try (bind (eval_stmts (cx with stk updated_by CONS (NONE,name)) ss)
                      (\u. return NoneV)) handle_function locked` >>
      rename1 `try _ _ locked = (body_res,body_end)` >>
      Cases_on `body_res`
      >- (rename1 `try _ _ _ = (INL rv,_)` >> Cases_on `safe_cast rtv rv` >>
          Cases_on `nr /\ mut <> View /\ mut <> Pure` >>
          Cases_on `cx.nonreentrant_slot` >>
          simp[finally_unless_halt_def,finally_def,pop_function_def,set_scopes_def,
               ignore_bind_def,bind_def,return_def,raise_def,unlock_if_nr_def,
               vyperTypeEvalStoragePreservationTheory.release_nonreentrant_lock_eq,
               lift_option_type_def] >> metis_tac[listTheory.MEM,listTheory.APPEND_NIL]) >>
      rename1 `try _ _ _ = (INR err,_)` >> Cases_on `err` >>
      Cases_on `nr /\ mut <> View /\ mut <> Pure` >>
      Cases_on `cx.nonreentrant_slot` >>
      simp[finally_unless_halt_def,finally_def,pop_function_def,set_scopes_def,
           ignore_bind_def,bind_def,return_def,raise_def,unlock_if_nr_def,
           vyperTypeEvalStoragePreservationTheory.release_nonreentrant_lock_eq] >>
      metis_tac[listTheory.MEM,listTheory.APPEND_NIL]) >>
  qexists_tac `[]` >>
  asm_simp_tac bool_ss [intcall_rest_def,intcall_callee_src_def,ignore_bind_def,
    bind_def,pairTheory.pair_case_thm,sumTheory.sum_case_def,listTheory.MEM,
    listTheory.APPEND_NIL,pairTheory.SND]
QED

Theorem intcall_rest_trace_request[local]:
  (SND (intcall_rest cx name mut nr ss prev rtv st)).storage_trace =
    obs_pre ++ StorageOutcome rq outcome :: sfx ==>
  ?rest. (SND (intcall_callee_src cx name mut nr ss st)).storage_trace =
    obs_pre ++ StorageOutcome rq outcome :: rest
Proof
  strip_tac >>
  qspecl_then [`cx`,`name`,`mut`,`nr`,`ss`,`prev`,`rtv`,`st`]
    strip_assume_tac intcall_rest_trace_suffix >>
  `obs_pre ++ [StorageOutcome rq outcome] ++ sfx =
    (SND (intcall_callee_src cx name mut nr ss st)).storage_trace ++ suffix` by
      (pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,listTheory.APPEND] >> metis_tac[]) >>
  qpat_x_assum `obs_pre ++ [_] ++ _ = _`
    (strip_assume_tac o REWRITE_RULE [listTheory.APPEND_EQ_APPEND_MID])
  >- (qexists_tac `l` >>
      qpat_x_assum `_ = obs_pre ++ [_] ++ l` mp_tac >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,listTheory.APPEND] >> simp[]) >>
  qpat_assum `!rq outcome. ~MEM _ suffix` (qspecl_then [`rq`,`outcome`] mp_tac) >>
  qpat_assum `suffix = _` (pure_rewrite_tac o single) >>
  simp[listTheory.MEM_APPEND]
QED

Theorem intcall_invoke_focus:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  ptr_inst_ok D lo 0 ctx func G tn inst t /\
  gas_origin_ptr_focus (D,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks stop ==>
  gas_origin_ptr_focus (D,lo,explicit,ctx,func,PG) (t,G,tn) marks stop
Proof
  PairCases_on `stop` >> strip_tac >>
  `inst.inst_opcode = INVOKE` by gvs[gas_invoke_entry_def] >>
  irule (cj 3 gas_origin_ptr_focus_rules) >>
  first_assum (irule_at Any) >> metis_tac[]
QED

Theorem intcall_return_request_prefix:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,arg_ops) /\
  (!H. ptr_inst_ok (DF H) lo 0 ctx func G tn inst t) /\
  gas_prefix_full (DF,lo,explicit,ctx,callee,MAP (op_prov G) arg_ops)
    cx st0 (intcall_callee_src cx name mut nr ss)
    (es1,entered,FEMPTY,tn with t_var := FEMPTY) ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG)
    cx st0 (intcall_rest cx name mut nr ss prev rtv) (es1,t,G,tn)
Proof
  simp[gas_prefix_full_def] >> strip_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by metis_tac[gas_invoke_entry_readings] >>
  rename1 `gas_origin_ptr_focus _ _ marks (leaf,leaf_pg,leaf_g,leaf_tn,stop_state)` >>
  qexists_tac `marks` >> conj_tac
  >- (qexistsl_tac [`H`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`stop_state`] >>
      simp[] >> irule intcall_invoke_focus >>
      qhdtm_assum `gas_origin_ptr_focus` (irule_at Any) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `(SND (intcall_rest cx name mut nr ss prev rtv
     (es1 with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail))).storage_trace =
      obs_pre ++ StorageOutcome rq outcome :: sfx` by simp[] >>
  drule_then strip_assume_tac intcall_rest_trace_request >>
  Cases_on `intcall_callee_src cx name mut nr ss
     (es1 with gas_obs := gas_explicit marks t.vs_gas_readings ++ tail)` >>
  gvs[] >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _ ==> request_site _ _ _ _ _ _ _`
    (drule_all_then (strip_assume_tac o REWRITE_RULE [request_site_def])) >>
  rewrite_tac[request_site_def] >>
  qexistsl_tac [`left`,`leaf'`,`leaf_pg'`,`G'`,`tn'`,`t'`,`inst'`,`fuel`,`t''`] >>
  simp[] >> irule intcall_invoke_focus >>
  qpat_assum `gas_origin_ptr_focus _ _ left _` (irule_at Any) >> simp[]
QED
