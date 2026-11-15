(* Saved scalar arguments transported to the selected positional endpoint. *)
Theory bodyFullExtCallRequestSavedStack
Ancestors
  bodyFullGhostFrame exprSimVVFrame logValueFramePtr
  bodyFullExtCallRequestPositional
  exprSimProps exprSimDefs exprSimMemDefs loweringPosts bodyPtrDefs
  loweringStateRelDefs venomState vyperState context compileEnv
  exprLoweringProps freshWrites finite_map words list

Theorem extcall_request_saved_stack_endpoint:
  (?raw. read_result cx raw mid = (INL v,mid) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw (StackValue tag op) mid t /\
    vv_at cenv cx (lowered_value_type cenv e) sa sm mid raw (StackValue tag op) t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw (StackValue tag op) mid G1 tn1 t /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) mid raw (StackValue tag op) t) /\
  (~is_word_type (lowered_value_type cenv e) ==> ptr_buf_ok cenv e op G1 t) /\
  ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  pure_frame cenv func mid sm t u /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  alloca_inv u /\ t.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_labels = t.vs_labels /\
  (!n b sz. local_region cenv mid.scopes t n b sz <=> local_region cenv ee.scopes u n b sz) /\
  ee.scopes = mid.scopes ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds cenv cx (lowered_value_type cenv e) raw (StackValue tag op) ee u /\
    vv_at cenv cx (lowered_value_type cenv e) sa sb ee raw (StackValue tag op) u /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw (StackValue tag op) ee G2 tn2 u /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw (StackValue tag op) u) /\
  (~is_word_type (lowered_value_type cenv e) ==> ptr_buf_ok cenv e op G2 u)
Proof
  strip_tac >>
  `expr_val_rel cx (lowered_value_type cenv e) v op t /\
   expr_val_at cenv cx (lowered_value_type cenv e) sa sm mid v op t /\
   ptr_val_ok cx (lowered_value_type cenv e) v op G1 tn1 t` by
    gvs[vv_holds_def, vv_at_def, ptr_vv_ok_def] >>
  `?w. eval_operand op t = SOME w` by gvs[expr_val_rel_def] >>
  `eval_operand op u = SOME w` by
    (Cases_on `op` >> gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operand op u = eval_operand op t` by simp[] >>
  `!tv. ~is_word_type (lowered_value_type cenv e) /\
     evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv ==>
     val_wf tv v /\
     mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory /\
     (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn2.t_mem ==>
       i IN tn1.t_mem)` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (gvs[expr_val_at_def] >> metis_tac[]) >>
     conj_tac
     >- (drule_all expr_val_at_pure_frame_bytes >> simp[]) >>
     rpt strip_tac >>
     drule_all (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:num # num``]
       expr_val_at_ghost_kept_at_taint) >> simp[]) >>
  `(!x. op = Var x ==> FLOOKUP G2 x = FLOOKUP G1 x) /\
   op_taint tn2 op = op_taint tn1 op` by
    (gvs[ghost_kept_at_def] >> Cases_on `op` >>
     gvs[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (strip_tac >> irule ptr_buf_ok_frame >>
      qexistsl_tac [`G1`, `t`] >> simp[]) >>
  qexists_tac `Value v` >>
  simp[vv_holds_def, vv_at_def, ptr_vv_ok_def, read_result_def, return_def] >>
  conj_tac
  >- (gvs[expr_val_rel_def] >>
      rpt gen_tac >> strip_tac >> Cases_on `is_word_type (lowered_value_type cenv e)`
      >- (gvs[] >> metis_tac[]) >>
      gvs[] >> irule val_in_memory_footprint_agree >> simp[] >> qexists_tac `t.vs_memory` >>
      metis_tac[]) >>
  conj_tac
  >- (gvs[expr_val_at_def, ci_mono_def] >> rpt gen_tac >> strip_tac >>
      qpat_x_assum `!tv. _ ==> (?(aid:num) b sz. _) \/ _` drule >>
      simp[] >> strip_tac
      >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >>
          simp[] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
      >- metis_tac[] >> simp[]) >>
  conj_tac
  >- (irule ptr_val_ok_footprint_frame >>
      qexistsl_tac [`G1`, `t`, `tn1`] >> simp[] >> metis_tac[]) >>
  gvs[vv_store_bound_def, read_result_def, return_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED
