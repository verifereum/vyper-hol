(* The body frame at the actual selected or fallback registration result. *)
Theory runtimeEntryBodyFrame
Ancestors
  externalBodyFrame runtimeBodyStartDefs runtimeFallbackSourceAlignment
  runtimeFallbackPackageEnvironment

Theorem runtime_entry_body_frame:
  !tops rpolicy unit am tx ret vs mut args fbody env es0 lbl cenv_ext cenv0 pos_args
   min_cds is_payable nkey ut' iv rt st cenv sa.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,F,args,[],ret,fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <|outcomes := SOME vs.vs_outcomes; requests := []|>) = (INL (),es0) /\
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
         (mut,F,lookup_raw_return_or_F (NONE:num option)
                     tx.function_name External tops,
          tx.function_name,args,([]:expr list),ret,fbody)) =
      (lbl,cenv_ext,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) /\
    ((cenv0 = cenv_ext /\
      runtime_selected_body_start tops rpolicy
        (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) st) \/
     (tx.function_name = "__default__" /\ args = [] /\
      pos_args = [] /\ min_cds = 4 /\
      cenv_ext = (if ret <> NoneT then update_cenv_ret_abi cenv0 ret else cenv0) /\
      runtime_fallback_body_start tops rpolicy
        (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut',iv,fbody,rt) st)) /\
    compile_register_positional_args cenv0 pos_args 4 st = (cenv,sa) ==>
    body_inv tops unit.cu_context cenv
      (initial_evaluation_context am.sources am.layouts tx NONE) /\
    cenv.ce_return_pc = NONE /\
    ?bindings env_t env'.
      supported_stmts tops bindings fbody /\
      expr_sim_inv cenv
        (initial_evaluation_context am.sources am.layouts tx NONE) env_t es0 /\
      ce_locals_declared cenv env_t /\ locals_alloc_ok cenv env_t /\
      type_stmts env_t ret fbody = SOME env' /\
      stmts_exprs_ok cenv fbody /\
      call_evaluation_safe
        (initial_evaluation_context am.sources am.layouts tx NONE)
        (int_calls_stmts fbody)
Proof
  rpt gen_tac >> strip_tac
  >- (gvs[] >>
      drule_all (INST_TYPE [alpha |-> ``:expr``] external_body_frame) >> simp[]) >>
  qpat_x_assum `runtime_fallback_body_start _ _ _ _` mp_tac >>
  simp[ runtime_fallback_body_start_def ] >> strip_tac >>
  `FST (SND (SND (classify_functions tops))) = SOME fb` by simp[] >>
  drule_all classified_fallback_source_alignment >> strip_tac >>
  gvs[] >>
  drule_all same_source_fallback_package_environment >> strip_tac >>
  qpat_x_assum `cenv0 = if _ then _ else _` (SUBST_ALL_TAC o SYM) >>
  irule (INST_TYPE [alpha |-> ``:expr``] external_body_frame) >> simp[] >>
  rpt (goal_assum (drule_at Any) >> simp[])
QED
