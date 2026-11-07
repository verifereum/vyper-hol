(*
 * Storage invariants across an internal call's omitted defaults
 *
 * The source evaluates the omitted defaults of an internal call in the
 * caller, after the arguments, in an empty frame (scopes [FEMPTY]) with
 * the callee on the call stack, and then restores the caller's scopes.
 * Given that the defaults' evaluation keeps storage well formed (the
 * caller's induction hypothesis), the caller's storage invariants and
 * argument typing survive it, and the oracle stream only advances.
 *
 * TOP-LEVEL:
 *   intcall_defaults_oracle_storage
 *)

Theory bodyStorageIntcallDefaults
Ancestors
  vyperCall vyperAST vyperInterpreter vyperState vyperTypeSystem
  vyperTypeExprSoundness vyperTypeEvalSoundness vyperTypeStoragePreservation
  vyperStorageLayoutSafety vyperEvalOutcomeSuffix vyperTypeEvalStoragePreservation
  bodyStorageCases list

Theorem intcall_defaults_oracle_storage:
  well_typed_exprs (defaults_env env_body) dflts /\
  env_body.current_src = NONE /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members /\
  runtime_storage_consistent env cx st /\ functions_well_typed cx /\
  call_evaluation_safe (cx with stk updated_by CONS (NONE,fn))
    (int_calls_exprs (DROP n dflts)) /\
  IS_SOME st.outcomes /\ oracle_storage_ok cx st /\
  expr_results_typed (env,cx,st) es results /\
  (!r1 s1. eval_exprs (cx with stk updated_by CONS (NONE,fn)) (DROP n dflts)
             (st with scopes := [FEMPTY]) = (r1,s1) ==>
           contract_storage_well_formed cx s1) /\
  finally (do set_scopes [FEMPTY];
              eval_exprs (cx with stk updated_by CONS (NONE,fn)) (DROP n dflts) od)
    (set_scopes st.scopes) st = (res,st') ==>
  st'.scopes = st.scopes /\
  runtime_storage_consistent env cx st' /\
  IS_SOME st'.outcomes /\ oracle_storage_ok cx st' /\
  expr_results_typed (env,cx,st') es results
Proof
  strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  qpat_assum `runtime_consistent env cx st`
    (strip_assume_tac o REWRITE_RULE [runtime_consistent_def]) >>
  mp_tac (Q.INST [`src_id_opt` |-> `NONE`]
            intcall_defaults_runtime_storage_consistent) >>
  impl_tac >- simp[] >> strip_tac >>
  `runtime_consistent (defaults_env env_body)
     (cx with stk updated_by CONS (NONE,fn)) (st with scopes := [FEMPTY])` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `!r fs. eval_exprs (cx with stk updated_by CONS (NONE,fn)) (DROP n dflts)
            (st with scopes := [FEMPTY]) = (r,fs) ==>
     state_well_typed fs /\
     env_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (NONE,fn)) fs /\
     accounts_well_typed fs.accounts /\ no_type_error_result r /\
     (case r of INL vs => exprs_runtime_typed (defaults_env env_body) (DROP n dflts) vs
              | INR _ => T)` by
    (rpt gen_tac >> strip_tac >>
     irule (cj 1 (SPEC_ALL (cj 6 eval_scc_type_sound_results_mutual))) >>
     fs[runtime_consistent_def, well_typed_exprs_DROP] >>
     goal_assum (drule_at Any) >> simp[]) >>
  mp_tac (Q.INST [`src_id_opt` |-> `NONE`, `needed` |-> `DROP n dflts`,
                  `base_st` |-> `st`] intcall_defaults_restored_sound) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  drule default_frame_eval_result >> strip_tac >>
  qpat_x_assum `!r1 s1. _ ==> contract_storage_well_formed _ _` drule >>
  strip_tac >>
  `contract_storage_well_formed cx st'` by
    (irule contract_storage_well_formed_backends_frame >>
     qexists_tac `framed_st` >> simp[]) >>
  `outcome_suffix st.outcomes st'.outcomes` by
    (drule (cj 6 eval_outcome_suffix_mutual) >> simp[]) >>
  `runtime_consistent env cx st'` by simp[runtime_consistent_def] >>
  drule_all body_oracle_storage_entry_transfer >> simp[]
QED
