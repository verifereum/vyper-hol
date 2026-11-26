(* Connect the selected runtime entry to the body request-prefix simulation. *)
Theory s1PrefixBodyStart
Ancestors
  s1PrefixBodyStartEvidence s1PrefixLockAbort s1PrefixSelectedBoundFrame

Theorem runtime_prefix_body_start_cases:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\
  outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  (ctx_has_dalloca unit.cu_context ==>
   !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
               dalloca_fmp_headroom inst s) /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args dflts ret
    (subst_consts_stmts (module_consts_env tops []) fbody) ==>
  ?cx entry func marks G0 tn0 s0.
    cx = initial_evaluation_context am.sources am.layouts tx NONE /\
    entry = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    storage_trace_domain cx (initial_state am []) es0.storage_trace /\
    (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot) /\
    (!tail. external_entry_bound tops am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings ++ tail) mut args dflts
      (es0 with gas_obs := tail)) /\
    gas_origin_ptr_focus
      (cx_dead (storage_trace_horizon es0.storage_trace) cx,0,
       gas_explicit_sites unit.cu_context shadow_unit.cu_context,unit.cu_context,func,[])
      (entry,FEMPTY,entry_taint) marks (func,[],G0,tn0,s0) /\
    ((?exc es_abort.
        lock_if_nr cx nr (is_view_mut mut) es0 = (INR exc,es_abort) /\
        unit_prefix_cert shadow_unit.cu_context tops am tx unit vs) \/
     (?es_lock. lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
        (storage_trace_domain cx (initial_state am []) es_lock.storage_trace ==>
         ?compiled_body shadow_func cenv RetQ sl sb shadow_sl shadow_sb t G tn cenv'.
           compiled_body = subst_consts_stmts (module_consts_env tops []) fbody /\
           (!gas. eval_stmts cx compiled_body (es_lock with gas_obs := gas) =
                  eval_stmts cx fbody (es_lock with gas_obs := gas)) /\
           t.vs_gas_readings = DROP (LENGTH marks) vs.vs_gas_readings /\
           (!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
             gas_origin_ptr_path
               (cx_dead H cx,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,
                unit.cu_context,func,[]) (entry,FEMPTY,entry_taint) marks (OK t,G,tn)) /\
           frame_ret_ok_full ((\H. cx_dead H cx),0,NONE,unit.cu_context,
             shadow_unit.cu_context,[],func,shadow_func) cx RetQ cenv ret /\
           stmt_frag_prefix ((\H. cx_dead H cx),0,NONE,unit.cu_context,
              shadow_unit.cu_context,[],func,shadow_func) cx NoLoop RetQ cenv
             (stmts_env cenv NoLoop ret compiled_body)
             (stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body))
             (eval_stmts cx compiled_body) es_lock /\
           stmt_frag_full_pre ((\H. cx_dead H cx),0,NONE,unit.cu_context,
              shadow_unit.cu_context,[],func,shadow_func) cx NoLoop RetQ cenv
             (stmts_env cenv NoLoop ret compiled_body)
             (stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body))
             (eval_stmts cx compiled_body) es_lock
             (initial_state am [],sl,sb,shadow_sl,shadow_sb,t,G,tn,cenv'))))
Proof
  strip_tac >>
  drule_all runtime_prefix_body_start_evidence >>
  disch_then (qx_choosel_then [`cx`,`entry`,`func`,`marks`,`G0`,`tn0`,`s0`] strip_assume_tac) >>
  qexistsl_tac [`cx`,`entry`,`func`,`marks`,`G0`,`tn0`,`s0`] >>
  asm_simp_tac std_ss []
  >- (qpat_assum `!tail. external_entry_bound _ _ _ _ _ _ _ _ _`
        (qspec_then `[]` assume_tac) >>
      drule_all selected_bound_request_frame >> simp[] >> strip_tac >>
      metis_tac[selected_lock_abort_prefix_cert])
  >- gvs[]
QED
