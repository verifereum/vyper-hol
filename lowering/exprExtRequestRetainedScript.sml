(* Retained keyword operands: allocation provenance makes history transport safe. *)
Theory exprExtRequestRetained
Ancestors
  exprExtRequestHistory exprExtRequestReconstruct exprSafeOperand exprSimProps
  loweringPosts compileEnv loweringStateRelDefs freshWrites valueEncodingProofs abiCallerAllocation
  exprLoweringProps venomState

Definition extrequest_retained_value_def:
  extrequest_retained_value cenv cx ty v op ee sc t <=>
    safe_operand sc op /\ expr_val_rel cx ty v op t /\
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v /\ val_wf tv v /\
      (~is_word_type ty ==> ?w aid size.
        eval_operand op t = SOME w /\ aid < sc.cs_next_id /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,size) /\
        val_footprint tv v <= size /\
        w2n w + val_footprint tv v <= t.vs_alloca_next /\
        (!name b sz. local_region cenv ee.scopes t name b sz ==>
          loweringStateRelDefs$regions_disjoint (w2n w) size b sz))
End

Theorem extrequest_retained_value_transport:
  extrequest_retained_value cenv cx ty v op ec sc tc /\
  extrequest_history_frame cenv cx ec sc tc ee sn t /\
  stmt_state_rel ctx func cenv cx ec tc /\
  stmt_state_rel ctx func cenv cx ee t ==>
  extrequest_retained_value cenv cx ty v op ee sn t
Proof
  strip_tac >>
  `safe_operand sn op` by
    (irule safe_operand_mono >>
     qexists_tac `sc` >>
     gvs[extrequest_retained_value_def, extrequest_history_frame_def]) >>
  Cases_on `is_word_type ty`
  >- (gvs[extrequest_retained_value_def] >>
      qpat_x_assum `expr_val_rel cx ty v op tc` mp_tac >>
      simp[expr_val_rel_def] >> strip_tac >>
      drule_all extrequest_history_operand >> strip_tac >>
      metis_tac[]) >>
  fs[extrequest_retained_value_def] >>
  rename1 `FLOOKUP tc.vs_allocas aid = SOME (w2n w,buf_size)` >>
  `eval_operand op t = SOME w` by
    (drule_all extrequest_history_operand >> simp[]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) tc.vs_memory` by
    (irule extrequest_history_alloc_window >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     simp[GSYM regions_disjoint_def] >> metis_tac[]) >>
  `expr_val_rel cx ty v op t` by
    (irule expr_val_rel_footprint_agree >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas aid = SOME (w2n w,buf_size)` by
    (gvs[extrequest_history_frame_def] >> metis_tac[]) >>
  `alloca_inv t` by gvs[stmt_state_rel_def] >>
  `w2n w + val_footprint tv v <= t.vs_alloca_next` by
    (irule abi_caller_allocation_end >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[] >> qexistsl_tac [`aid`, `buf_size`] >>
  conj_tac >- gvs[extrequest_history_frame_def] >>
  simp[] >> rpt strip_tac >>
  `local_region cenv ec.scopes tc name b sz` by
    (drule_all extrequest_history_local_regions >> metis_tac[]) >>
  metis_tac[]
QED
