Theory abiEncTuplePtrUncapturedCapacity
Ancestors
  abiEncTuplePtrUncapturedRec bodyPtrTypeBuiltinsTransport
  abiEncodeArgsSim wordArgsPtr stmtFragPtr argsTailPtr
  abiEncTuplePtrArgLayout bodyPtrBytestringBuiltinsEval
  abiEncTuplePtrArgTransport exprSimAbiEncodeArgsCaptured
  exprSimAbiEncodeArgsMaterializePath exprSimProps
  exprSimWordArgs exprLoweringProps loweringStateRelDefs bodyPtrDefs
  fragGasPathPtr gasSummary vyperState loweringPosts list
  abiEncTuplePtrArgsContext gasSummaryComposePtr
  abiEncodeArgsScopes exprSimSliceCapture exprSimSource exprSimHyps
  exprSimLayoutTransport vyperEvalExprPreservesScopesDom

Theorem abi_args_uncaptured_cons_capacity_ptr[local]:
  expr_post ctx func ce cx e es sa sm s0 es1 v op t /\
  expr_val_rel cx (lowered_value_type ce e) v op t /\
  expr_val_at ce cx (lowered_value_type ce e) sa sm es1 v op t /\
  ptr_val_ok cx (lowered_value_type ce e) v op G1 tn1 t /\
  (~is_word_type (lowered_value_type ce e) ==> ptr_buf_ok ce e op G1 t) /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  expr_sim_inv ce cx env es1 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG (eval_exprs cx args)
    (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) ops (ZIP (args,vs)) /\
      LIST_REL (\op e. ~is_word_type (lowered_value_type ce e) ==>
        ptr_buf_ok ce e op G u) ops args /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
      MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
      (~is_word_type (lowered_value_type ce e) ==> ee.scopes = es1.scopes) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es1 sm G1 tn1 t G tn)
    (\rr ee ghosts r. wb_args_exit rr r) ==>
  gas_outcome_ptr D (cx_tops cx) (ctx,func) PG
    (bind (eval_exprs cx args) (\vs. return (v::vs))) (es1,t,G1,tn1)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) (op::ops) (ZIP (e::args,vs)) /\
      LIST_REL (\op e. ~is_word_type (lowered_value_type ce e) ==>
        ptr_buf_ok ce e op G u) (op::ops) (e::args) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> irule gas_outcome_ptr_return_map >>
  goal_assum (drule_at Any) >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      conj_tac
      >- (irule abi_args_post_cons_uncaptured >>
          gvs[ci_mono_def] >> metis_tac[]) >>
      conj_tac
      >- (Cases_on `is_word_type (lowered_value_type ce e)`
          >- (drule_all ghost_kept_operand >>
              Cases_on `op` >>
              gvs[ptr_val_ok_def, ghost_kept_def, ptrDisciplineTheory.op_prov_def, not_fresh_at_def]) >>
          `stmt_state_rel ctx func ce cx es1 t` by
            metis_tac[expr_post_def] >>
          `stmt_state_rel ctx func ce cx ee t' /\
           wb_frame ce es1 ee sm t t'` by metis_tac[abi_args_post_def] >>
          gvs[] >> irule abi_args_uncaptured_operand_ptr_transport >>
          qpat_assum `expr_val_at _ _ _ _ _ _ _ _ t` (irule_at Any) >>
          qpat_assum `ghost_kept _ es1 sm _ _ t _ _` (irule_at Any) >>
          simp[] >> metis_tac[]) >>
      conj_tac
      >- (strip_tac >> irule ptr_buf_ok_ghost_kept >>
          qpat_assum `ghost_kept _ es1 sm _ _ t _ _` (irule_at Any) >>
          simp[] >>
          `wb_frame ce es1 ee sm t t'` by metis_tac[abi_args_post_def] >>
          `?w. eval_operand op t = SOME w` by metis_tac[expr_val_rel_def] >>
          drule_all abi_args_operand_kept >> simp[]) >>
      conj_tac >- metis_tac[abi_args_operand_live] >>
      `wb_frame ce es es1 sa s0 t` by
        (gvs[expr_post_def, wb_frame_def] >> metis_tac[]) >>
      gvs[ci_mono_def] >> drule_all ghost_kept_wb_trans >> simp[]) >>
  Cases_on `rr` >> simp[wb_args_exit_def]
QED

Theorem abi_args_uncaptured_head_capacity_ptr[local]:
  expr_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  expr_body_pre ce cx env e es /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  (!gs v es1.
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
    expr_sim_inv ce cx env es1 /\
    (~is_word_type (expr_type e) ==>
      ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
           value_has_type tv v /\ val_wf tv v)) /\
  (!v es1 G1 tn1 t.
    (?gs. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,es1)) /\
    stmt_state_rel ctx func ce cx es1 t /\ ghost_inv d ce cx es1 G1 tn1 t /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_exprs cx args)
      (es1,t,G1,tn1)
      (\rr ee G tn u. ?vs. rr = INL vs /\
        abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
        LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
          (SND ev) op G tn u) ops (ZIP (args,vs)) /\
        LIST_REL (\op e. ~is_word_type (lowered_value_type ce e) ==>
          ptr_buf_ok ce e op G u) ops args /\
        EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
        MAP FDOM ee.scopes = MAP FDOM es1.scopes /\
        (~is_word_type (lowered_value_type ce e) ==> ee.scopes = es1.scopes) /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv d ce cx ee G tn u /\ ghost_kept ce es1 sm G1 tn1 t G tn)
      (\rr ee ghosts r. wb_args_exit rr r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (e::args)) (es,s0,G0,tn0)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) (op::ops) (ZIP (e::args,vs)) /\
      LIST_REL (\op e. ~is_word_type (lowered_value_type ce e) ==>
        ptr_buf_ok ce e op G u) (op::ops) (e::args) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> rewrite_tac[eval_exprs_cons_action] >>
  irule expr_sim_ptr_eval_suffix >>
  qpat_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ _ _ = _` (irule_at Any) >>
  simp[] >> conj_tac >- simp[oneline exprSimDefsTheory.expr_exit_def, wb_args_exit_def] >>
  rpt gen_tac >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre ce cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `expr_sim_inv ce cx env ee /\
   (~is_word_type (expr_type e) ==>
     ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
          value_has_type tv v /\ val_wf tv v)` by metis_tac[] >>
  `expr_val_rel cx (lowered_value_type ce e) v op t` by
    (irule abi_args_expr_post_lowered_rel >> metis_tac[]) >>
  `expr_val_at ce cx (lowered_value_type ce e) sa sm ee v op t` by
    (irule abi_args_expr_post_lowered_at >> metis_tac[]) >>
  `ptr_val_ok cx (lowered_value_type ce e) v op G tn t` by
    (irule abi_args_ptr_lowered_transport >> metis_tac[]) >>
  `~is_word_type (lowered_value_type ce e) ==> ptr_buf_ok ce e op G t` by
    (strip_tac >>
     `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
       metis_tac[expr_body_pre_lowered_fits] >>
     `~is_word_type (expr_type e)` by metis_tac[compatible_word_type] >>
     drule_all abiEncodeMaterializeTheory.materialize_post_lowered_classify >>
     metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  irule (SRULE [] abi_args_uncaptured_cons_capacity_ptr) >>
  qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >> simp[] >>
  qexists `env` >> conj_tac >- metis_tac[exprSimHypsDefsTheory.expr_sim_inv_gas_obs] >>
  gvs[] >> qpat_x_assum `!v es1 G1 tn1 t. _`
    (qspecl_then [`v`, `ee0 with gas_obs := []`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> conj_tac
  >- (qexists `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >> simp[expr_post_def]
QED

Theorem abi_args_uncaptured_rec_capacity_ptr:
  abi_args_ready ctx func ce cx Inv (e::args) /\ Inv es /\
  (!s. Inv s ==> expr_sim_inv ce cx env s) /\
  (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
  expr_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  unwrap_value ce vv mid = (op,sm) /\
  compile_abi_encode_args compile_expr ce args sm = (ops,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ~(~is_word_type (expr_type e) /\ exprs_can_mutate ce args) /\
  (!es1 sa1 ops1 sb1 t G1 tn1.
    abi_args_ready ctx func ce cx Inv args /\ Inv es1 /\
    compile_abi_encode_args compile_expr ce args sa1 = (ops1,sb1) /\
    fn_has_code sa1 sb1 func /\ local_ptrs_reserved ce sa1 /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa1 x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa1 x) /\
    stmt_state_rel ctx func ce cx es1 t /\ ghost_inv d ce cx es1 G1 tn1 t /\
    ~t.vs_halted /\ t.vs_current_bb = sa1.cs_current_bb /\
    t.vs_inst_idx = LENGTH sa1.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG (eval_exprs cx args)
      (es1,t,G1,tn1)
      (\rr ee G tn u. ?vs. rr = INL vs /\
        abi_args_post ctx func ce cx es1 sa1 sb1 t ee args ops1 vs u /\
        LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
          (SND ev) op G tn u) ops1 (ZIP (args,vs)) /\
        LIST_REL (\op e. ~is_word_type (lowered_value_type ce e) ==>
          ptr_buf_ok ce e op G u) ops1 args /\
        EVERY (abi_decoder_operand_live sb1.cs_next_var) ops1 /\
        u.vs_current_bb = sb1.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb1.cs_current_insts /\
        ghost_inv d ce cx ee G tn u /\ ghost_kept ce es1 sa1 G1 tn1 t G tn)
      (\rr ee ghosts r. wb_args_exit rr r)) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (e::args)) (es,s0,G0,tn0)
    (\rr ee G tn u. ?vs. rr = INL vs /\
      abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
      LIST_REL (\op ev. ptr_val_ok cx (lowered_value_type ce (FST ev))
        (SND ev) op G tn u) (op::ops) (ZIP (e::args,vs)) /\
      LIST_REL (\op e. ~is_word_type (lowered_value_type ce e) ==>
        ptr_buf_ok ce e op G u) (op::ops) (e::args) /\
      EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d ce cx ee G tn u /\ ghost_kept ce es sa G0 tn0 s0 G tn)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all abi_args_compile_uncaptured_ptr_context >> strip_tac >>
  irule abi_args_uncaptured_head_capacity_ptr >> simp[] >>
  conj_tac >- metis_tac[slice_source_operand_not_label] >>
  reverse conj_tac
  >- (conj_tac >- metis_tac[expr_body_pre_gas_admissible] >>
      qexists `env` >> simp[] >> rpt strip_tac >>
      drule_all abi_args_success_ready_ptr >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all abi_args_success_ready_ptr >> strip_tac >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  qpat_x_assum `!es1 sa1 ops1 sb1 t G1 tn1. _` drule_all >> strip_tac >>
  dxrule bodyPtrBytestringBuiltinsEvalTheory.gas_outcome_ptr_eval_evidence >> strip_tac >>
  irule gasSummaryComposePtrTheory.gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >> gnvs[] >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
  conj_tac >- (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  strip_tac >> Cases_on `is_word_type (expr_type e)`
  >- (drule expr_body_pre_physical_type >> metis_tac[compatible_word_type]) >>
  `~exprs_can_mutate ce args` by metis_tac[] >>
  drule_all eval_exprs_no_mutation_scopes >> simp[]
QED
