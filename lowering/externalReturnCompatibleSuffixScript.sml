(* Produced bytestring bounds do not change the external return suffix. *)
Theory externalReturnCompatibleSuffix
Ancestors externalReturnSelectedSuffix externalReturnConsumerFit compileEnv
  externalReturnSelectedResources externalReturnSiteSemantics externalReturnSimpleSuffix
  externalReturnConsumerProbe externalReturnSuffixResult stmtSimDefs bodySim
  loweringPosts exprLowering vyperInterpreter typedMemoryCopy words
  valueCopyBytes exprLoweringProps vyperTypeSystem

Theorem return_consumer_suffix_bytestring:
  is_bytestring_type ret /\ is_bytestring_type phy /\ is_bytestring_type ann ==>
  return_consumer_suffix ce ret phy op sa =
  return_consumer_suffix ce ret ann op sa
Proof
  simp[return_consumer_suffix_def]
QED

Theorem return_selected_compatible_suffix:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  expr_post ctx func ce cx e es se sa s0 ee v op s /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target /\
  (lowered_value_type ce e = expr_type e \/
    (is_bytestring_type ret /\ is_bytestring_type (lowered_value_type ce e) /\
     is_bytestring_type (expr_type e))) /\
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
  >- (drule_all return_selected_located_suffix >> simp[]) >>
  drule_all return_selected_consumer_resources >> strip_tac >>
  `~is_word_type ret` by metis_tac[is_bytestring_word_type] >>
  (Q.SUBGOAL_THEN `expr_type e = ret \/
    (is_bytestring_type (expr_type e) /\ is_bytestring_type ret)` assume_tac
    >- simp[]) >>
  Cases_on `ce.ce_raw_return`
  >- (drule_all return_site_value_semantics >> strip_tac >>
      drule_all return_site_nocopy_memory >> strip_tac >>
      `compile_external_return (SOME op) F T ce.ce_ret_enc_info
         ce.ce_max_return_size F nkey F (mut = View) sa = (u,sf)` by
        (qpat_x_assum `return_consumer_suffix _ _ _ _ _ = _` mp_tac >>
         gvs[return_consumer_suffix_def, comp_bind_def, comp_return_def]) >>
      `state_rel func ce cx ee s` by fs[stmt_state_rel_def] >>
      `lookup_raw_return_or_F (NONE:num option) tx.function_name External tops`
        by fs[] >>
      gvs[] >> rename1 `val_in_memory rtv v (w2n w) s.vs_memory` >>
      `w2n w + val_footprint rtv v <= dimword (:256)` by simp[] >>
      drule_all return_raw_suffix_path >> strip_tac >>
      first_x_assum (qspecl_then [`am.exports`, `ctx`] strip_assume_tac) >>
      qexistsl_tac [`n`, `r`] >> simp[] >> metis_tac[]) >>
  `ret <> NoneT` by metis_tac[return_site_valued_not_none] >>
  drule_all return_selected_nocopy_window >> strip_tac >>
  `ce.ce_max_return_size < dimword (:256)` by
    (drule_all return_site_output_buffer_bound >> simp[]) >>
  `compile_external_return (SOME op) F F ce.ce_ret_enc_info
     ce.ce_max_return_size F nkey F (mut = View) sa = (u,sf)` by
    (qpat_x_assum `return_consumer_suffix _ _ _ _ _ = _` mp_tac >>
     gvs[return_consumer_suffix_def, comp_bind_def, comp_return_def]) >>
  `?n r. gas_path ctx func s n r /\ exit_result r /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state am.sources am.exports am.layouts ee),
       ee.requests) r` by
    (irule return_abi_suffix_path >>
     qpat_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`n`, `r`] >> simp[] >> metis_tac[]
QED

Theorem return_bytestring_widening[local]:
  is_bytestring_type ty /\ type_widens_to tenv ty ret ==>
  is_bytestring_type ret
Proof
  namedCases_on `ty` ["bt", "ts", "et bd", "ns", "ns", ""] >>
  simp[oneline is_bytestring_type_def] >>
  Cases_on `bt` >> simp[oneline is_bytestring_type_def]
  >- (namedCases_on `ret` ["rb", "ts", "et bd", "ns", "ns", ""] >>
      simp[type_widens_to_def, arg_type_fits_def] >> Cases_on `rb` >>
      simp[arg_type_fits_def, oneline is_bytestring_type_def]) >>
  rename1 `BytesT bd` >> Cases_on `bd` >> simp[oneline is_bytestring_type_def] >>
  namedCases_on `ret` ["rb", "ts", "et bd", "ns", "ns", ""] >>
  simp[type_widens_to_def, arg_type_fits_def] >>
  namedCases_on `rb` ["k", "k", "", "", "k", "rd", ""] >>
  simp[arg_type_fits_def, oneline is_bytestring_type_def] >>
  Cases_on `rd` >> simp[arg_type_fits_def, oneline is_bytestring_type_def]
QED

Theorem return_ordinary_producer_compatible:
  well_typed_expr env e /\
  type_widens_to env.type_defs (expr_type e) ret /\
  (!ty fid es ks. e <> Call ty (IntCall fid) es ks) ==>
  lowered_value_type ce e = expr_type e \/
  (is_bytestring_type ret /\ is_bytestring_type (lowered_value_type ce e) /\
   is_bytestring_type (expr_type e))
Proof
  Cases_on `e` >> simp[lowered_value_type_def] >>
  rpt strip_tac >> gvs[well_typed_expr_def]
  >- (namedCases_on `t` ["bt", "ts", "et bd", "ns", "ns", ""] >>
      gvs[well_typed_literal_def] >> Cases_on `bt` >>
      Cases_on `l` >> gvs[well_typed_literal_def, lowered_value_type_def,
        vyperASTTheory.expr_type_def, is_bytestring_type_def]
      >- metis_tac[return_bytestring_widening, is_bytestring_type_def] >>
      rename1 `BytesT bd` >> Cases_on `bd` >>
      gvs[lowered_value_type_def, vyperASTTheory.expr_type_def, is_bytestring_type_def] >>
      metis_tac[return_bytestring_widening, is_bytestring_type_def])
  >- (Cases_on `t0` >>
      gvs[lowered_value_type_def, vyperASTTheory.expr_type_def,
          type_builtin_result_ok_def, is_bytestring_type_def] >>
      metis_tac[return_bytestring_widening, is_bytestring_type_def]) >>
  Cases_on `c` >> gvs[lowered_value_type_def]
QED

Theorem return_site_ordinary_compatible:
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  (!ty fid es ks. e <> Call ty (IntCall fid) es ks) ==>
  lowered_value_type ce e = expr_type e \/
  (is_bytestring_type ret /\ is_bytestring_type (lowered_value_type ce e) /\
   is_bytestring_type (expr_type e))
Proof
  strip_tac >> irule return_ordinary_producer_compatible >>
  gvs[type_stmt_def, AllCaseEqs()] >> metis_tac[]
QED
