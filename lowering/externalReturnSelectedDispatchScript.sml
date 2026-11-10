(* Applicability of the selected suffix to all successful producer tags. *)
Theory externalReturnSelectedDispatch
Ancestors externalReturnSelectedPrefix externalReturnCompatibleSuffix
  externalReturnDeclarationProvenance externalReturnPhysicalMetadata
  externalReturnSelectedSuffix exprSimHypsDefs loweringPosts
  vyperTypeSystem exprLowering

Theorem return_selected_success_suffix:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops ut nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es se sa s0 ee v op s /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  ((!ann fid xs drv. e <> Call ann (IntCall fid) xs drv) \/
    (?ann fid xs drv. e = Call ann (IntCall fid) xs drv) \/
    (?ann fid xs drv pvs. e = Call ann (IntCall fid) xs drv /\
      ce.ce_func_info (nsid_to_string fid) = (0,0,pvs) /\ op = Lit 0w)) /\
  return_consumer_suffix ce ret (lowered_value_type ce e) op sa = (u,sf) /\
  fn_has_code sa sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ (!y. op = Var y ==> not_fresh_at sa y) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?n r. gas_path ctx func s n r /\ exit_result r /\
    (?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
Proof
  strip_tac
  >- (drule_all return_site_ordinary_compatible >>
      disch_then (qspec_then `ce` assume_tac) >>
      drule_all return_selected_compatible_suffix >> simp[])
  >- (gvs[] >>
      `well_typed_expr env (Call ann (IntCall fid) xs drv)` by
        gvs[type_stmt_def, AllCaseEqs()] >>
      `post_value_type ce (Call ann (IntCall fid) xs drv) <>
         lowered_value_type ce (Call ann (IntCall fid) xs drv) ==>
       is_bytestring_type (post_value_type ce (Call ann (IntCall fid) xs drv)) /\
       is_bytestring_type (lowered_value_type ce (Call ann (IntCall fid) xs drv))`
        by metis_tac[return_intcall_post_lowered] >>
      drule_all return_selected_located_suffix >> simp[]) >>
  gvs[] >> PairCases_on `fid` >>
  `well_typed_expr env (Call ann (IntCall (fid0,fid1)) xs drv)` by
    gvs[type_stmt_def, AllCaseEqs()] >>
  `env_consistent env
     (initial_evaluation_context am.sources am.layouts tx NONE) es` by
    fs[expr_sim_inv_def] >>
  drule_all return_selected_same_frame_return_table >> strip_tac >>
  drule_all return_runtime_physical_evaluate >> strip_tac >>
  drule_all return_runtime_physical_widens >> strip_tac >>
  `env.type_defs = get_tenv (initial_evaluation_context am.sources am.layouts tx NONE)` by
    fs[vyperTypeInvariantsTheory.env_consistent_def, vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `stmt_state_rel ctx func ce
    (initial_evaluation_context am.sources am.layouts tx NONE) ee s` by
    fs[expr_post_def] >>
  gvs[lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  irule return_selected_bufferless_suffix >>
  simp[] >>
  qpat_assum `IS_SOME (type_stmt _ _ _)` (irule_at Any) >>
  qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
  qpat_assum `expr_sim_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `ce.ce_func_info _ = _` (irule_at Any) >>
  simp[lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  qpat_assum `return_consumer_suffix _ _ _ _ _ = _` (irule_at Any) >>
  metis_tac[]
QED
