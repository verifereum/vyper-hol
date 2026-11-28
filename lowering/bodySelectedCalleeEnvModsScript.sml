Theory bodySelectedCalleeEnvMods
Ancestors
  bodyInvSplit intCallCallee allocLimitsProps compileUnit compileVyper
  compileEnv moduleLowering emitHelper constSubstMods pair finite_map
  vyperTypeEvalProofs vyperTypeInvariants bodyCallSupport

(* Entry capture and materialization only replace the return locations and
   the local variable map. The immutable reservation is installed separately. *)
Theorem selected_capture_env[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) ==>
  ce1 = ce with <|ce_return_buf := ce1.ce_return_buf;
                  ce_return_pc := ce1.ce_return_pc|>
Proof
  Cases_on `has_rb` >>
  simp[compile_internal_entry_prefix_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[compile_env_component_equality]
QED

Theorem selected_materialize_env[local]:
  !caps ce reserved ce2 materialized.
    materialize_internal_params ce caps reserved = (ce2,materialized) ==>
    ce2 = ce with ce_vars := ce2.ce_vars
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def] >>
  PairCases >> rpt gen_tac >> simp[materialize_internal_params_def] >>
  IF_CASES_TAC
  >- (Cases_on `FLOOKUP ce.ce_vars h0` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[]) >>
      rename1 `FLOOKUP ce.ce_vars h0 = SOME loc` >>
      Cases_on `loc` >>
      simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
      strip_tac >> first_x_assum drule >> simp[]) >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Theorem selected_package_env[local]:
  set_internal_package_target target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss_comp,rt) ==>
  ce = (build_compile_env_unit mods src Internal mut name args ret ss_comp T) with
    <|ce_is_ctor := deploy; ce_target := target; ce_raw_return := rr;
      ce_nonreentrant := (nr,global_nonreentrant_slot,T,mut = View)|>
Proof
  simp[subst_consts_fn_mods_def, package_internal_fn_unit_def,
       set_internal_package_target_def, update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[]
QED

Theorem selected_body_env_shape[local]:
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) ==>
  ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> =
    ce with <|ce_vars := ce2.ce_vars; ce_return_buf := ce2.ce_return_buf;
              ce_return_pc := ce2.ce_return_pc; ce_imm_alloca := imm;
              ce_alloca_locals := T|>
Proof
  strip_tac >>
  drule_then assume_tac selected_capture_env >>
  drule_then assume_tac selected_materialize_env >>
  simp[compile_env_component_equality] >>
  rpt conj_tac >>
  qpat_assum `ce2 = _` (fn th => simp[Once th]) >>
  qpat_assum `ce1 = _` (fn th => simp[Once th])
QED

Theorem selected_pushed_metadata[local]:
  contract_inv mods exps ctx caller cx /\ ALOOKUP mods src = SOME tops /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit_mods mods exps policy rbc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps policy = SOME unit) /\
  ctx = unit.cu_context /\
  ce = (build_compile_env_unit mods src Internal mut name args ret ss T) with
    <|ce_is_ctor := cx.in_deploy; ce_target := policy.rpol_target;
      ce_raw_return := rr; ce_nonreentrant := nrinfo|> /\
  body_ce = ce with <|ce_vars := vars; ce_return_buf := rb; ce_return_pc := rpc;
                      ce_imm_alloca := imm; ce_alloca_locals := T|> ==>
  contract_inv mods exps ctx body_ce (cx with stk updated_by CONS (src,name)) /\
  module_body_inv mods src tops body_ce (cx with stk updated_by CONS (src,name)) /\
  alloc_env_agree (build_compile_env_unit mods src Internal mut name args ret ss F) body_ce /\
  body_ce.ce_var_type = (build_compile_env_unit mods src Internal mut name args ret ss T).ce_var_type /\
  ~body_ce.ce_is_external
Proof
  strip_tac >>
  fs[contract_inv_def, module_body_inv_def, cenv_module_pins_mods_def,
     alloc_env_agree_def, get_tenv_stk_irrelevant,
     build_compile_env_unit_def, ELIM_UNCURRY] >>
  gvs[immutable_section_layout_mods_def] >>
  conj_tac >- (rpt strip_tac >> res_tac) >>
  conj_tac >- (qexistsl [`policy`, `unit`] >> simp[]) >>
  conj_tac
  >- (simp[NoAsms, linked_body_calls_resolved_def, context_function_live_context] >>
      qpat_assum `linked_body_calls_resolved _ cx`
        (ACCEPT_TAC o SIMP_RULE (srw_ss()) [linked_body_calls_resolved_def])) >>
  conj_tac >- (rpt strip_tac >> res_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> res_tac
QED

(* The package uses Internal storage conventions in both modes, including
   when the source declaration selected by the caller is an imported Deploy. *)
Theorem selected_materialized_body_env_mods:
  contract_inv mods exps ctx caller cx /\ ALOOKUP mods src = SOME tops /\
  (if cx.in_deploy then ?rbc. lower_vyper_deploy_unit_mods mods exps policy rbc = SOME unit
   else lower_vyper_runtime_unit_mods mods exps policy = SOME unit) /\
  ctx = unit.cu_context /\
  set_internal_package_target policy.rpol_target
    (package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy ilen
      (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,name,args,dflts,ret,ss))) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen',ss_comp,rt) /\
  compile_internal_entry_prefix ce params has_rb entry = ((ce1,caps,rpc),capture) /\
  materialize_internal_params ce1 caps reserved = (ce2,materialized) /\
  body_ce = ce2 with <|ce_imm_alloca := imm; ce_alloca_locals := T|> ==>
  contract_inv mods exps ctx body_ce (cx with stk updated_by CONS (src,name)) /\
  module_body_inv mods src tops body_ce (cx with stk updated_by CONS (src,name)) /\
  alloc_env_agree
    (build_compile_env_unit mods src Internal mut name args ret ss_comp F) body_ce /\
  body_ce.ce_var_type = (build_compile_env_unit mods src Internal mut name args ret ss_comp T).ce_var_type /\
  ~body_ce.ce_is_external
Proof
  strip_tac >>
  drule_all selected_body_env_shape >> disch_then (qspec_then `imm` assume_tac) >>
  drule_then assume_tac selected_package_env >>
  qpat_x_assum `body_ce = _` SUBST_ALL_TAC >>
  drule_all selected_pushed_metadata >> simp[]
QED
