(* RawLog's checked pointer simulations, assembled from its two data branches. *)
Theory rawLogPtr
Ancestors
  rawLogPtrFixedSim rawLogPtrDynamicSim exprStackPtr bodyPtrDefs bodyPtrPreds
  bodySimRawLogBodySource exprSimHypsDefs vyperAST exprLowering

Theorem raw_log_body_sim_ptr:
  body_exprs_ptr_ok cx args /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Call ann RawLog args dflt) es /\
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Call ann RawLog args dflt) es
Proof
  strip_tac >>
  `expr_sim_ptr d ctx PG func cenv cx ty (Call ann RawLog args dflt) es` by
    (simp[expr_sim_ptr_def] >> rpt strip_tac >>
     drule_all raw_log_body_lower_value >> strip_tac >> gvs[] >>
     drule raw_log_body_pre_shape >> strip_tac >> gvs[]
     >- (irule raw_log_fixed32_body_frag_ptr >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
     irule raw_log_dynamic_frag_ptr >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule expr_vv_sim_stack_ptr >> simp[] >>
  conj_tac >- (drule raw_log_body_compile_stack >> metis_tac[]) >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.lift_option_type_def,
       vyperStateTheory.type_check_def, vyperStateTheory.check_not_static_def,
       vyperStateTheory.assert_def, vyperStateTheory.raise_def,
       vyperStateTheory.push_log_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
