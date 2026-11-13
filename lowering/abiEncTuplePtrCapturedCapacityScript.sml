Theory abiEncTuplePtrCapturedCapacity
Ancestors
  abiEncTuplePtrCapturedRec bodyPtrTypeBuiltinsTransport
  abiEncTuplePtrCapturedHead abiEncTuplePtrCapturedPrefix abiEncTuplePtrArgsCompose
  abiEncTuplePtrArgsContext exprSimAbiEncodeArgsMaterializePath
  exprSimWordArgs vyperState abiEncodeArgsSim gasSummaryComposePtr
  bodyPtrBytestringBuiltinsEval vyperEvalExprPreservesScopesDom
  exprSimHyps freshWrites
  wordArgsPtr stmtFragPtr argsTailPtr abiEncTuplePtrArgTransport
  exprSimAbiEncodeArgsCaptured exprLoweringProps loweringStateRelDefs
  bodyPtrDefs loweringPosts fragGasPathPtr gasSummary exprSimProps
  exprSimWordArgs exprSimAbiEncodeArgsMaterializePath

Theorem abi_args_captured_cons_capacity_ptr[local]:
  materialize_owned_post ctx func ce cx e es sa mid sm s0 es1 v op tv t /\
  ptr_val_ok cx (lowered_value_type ce e) v op G1 tn1 t /\
  ptr_buf_ok ce e op G1 t /\
  ghost_kept ce es sa G0 tn0 s0 G1 tn1 /\
  stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  ci_mono sa sm /\ ci_mono sm sb /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\ val_wf tv v /\
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
  >- (rpt strip_tac >> gvs[] >> conj_tac
      >- (irule captured_owned_cons_post >> metis_tac[]) >>
      conj_tac
      >- (`wb_frame ce es1 ee sm t t'` by metis_tac[abi_args_post_def] >>
          irule abi_args_captured_operand_ptr_transport >>
          qpat_assum `ghost_kept _ es1 sm _ _ t _ _` (irule_at Any) >> simp[] >>
          qexists `ee` >> reverse conj_tac
          >- metis_tac[materialize_owned_post_def] >>
          rpt strip_tac >> gvs[] >>
          qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
            (strip_assume_tac o REWRITE_RULE [materialize_owned_post_def]) >>
          gvs[] >> qexistsl [`mid.cs_next_id`, `w2n w`, `type_memory_size tv`] >>
          simp[val_footprint_le] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      conj_tac
      >- (strip_tac >> irule ptr_buf_ok_ghost_kept >>
          qpat_assum `ghost_kept _ es1 sm _ _ t _ _` (irule_at Any) >> simp[] >>
          `wb_frame ce es1 ee sm t t'` by metis_tac[abi_args_post_def] >>
          `?w. eval_operand op t = SOME w` by metis_tac[materialize_owned_post_def] >>
          metis_tac[abi_args_operand_kept]) >>
      conj_tac >- metis_tac[abi_args_operand_live] >>
      `wb_frame ce es es1 sa s0 t` by metis_tac[materialize_owned_post_def] >>
      gvs[ci_mono_def] >> drule_all ghost_kept_wb_trans >> simp[]) >>
  Cases_on `rr` >> simp[wb_args_exit_def]
QED

Theorem abi_args_captured_head_capacity_ptr[local]:
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  ci_mono sa mid /\ ci_mono sa sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  (!gs v ee. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gs) = (INL v,ee) ==>
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv v /\ val_wf tv v /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64 /\
      type_memory_size tv + 64 < dimword (:256)) /\
  (!es_pre tvv v ee tv G tn r.
    expr_body_pre ce cx env e es_pre /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
      ~is_word_type (post_value_type ce e) ==>
      type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
      type_memory_size tvt < 2 ** 64) /\
    fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
    ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    vv_post ctx func ce cx e es sa mid s0 ee tvv vv r /\
    read_result cx tvv ee = (INL v,ee) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64 /\
    type_memory_size tv + 64 < dimword (:256) /\
    ghost_inv d ce cx ee G tn r /\
    ptr_vv_ok cx (post_value_type ce e) tvv vv ee G tn r /\
    (!t' a. vv = StackValue t' a /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e a G r) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G r) /\
    ghost_kept ce es sa G0 tn0 s0 G tn /\
    ~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb /\
    r.vs_inst_idx = LENGTH mid.cs_current_insts ==>
    ?H tm t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn r 0 H tm (OK t) /\
      materialize_owned_post ctx func ce cx e es sa mid sm s0 ee v op tv t /\
      ptr_val_ok cx (lowered_value_type ce e) v op H tm t /\
      ptr_buf_ok ce e op H t /\
      ghost_inv d ce cx ee H tm t /\ ghost_kept ce es sa G0 tn0 s0 H tm /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts) /\
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
  strip_tac >> rewrite_tac[eval_exprs_cons_action, bind_assoc] >>
  irule abi_args_vv_eval_suffix_ptr >>
  qpat_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >> simp[] >>
  conj_tac >- simp[oneline exprSimDefsTheory.expr_exit_def, wb_args_exit_def] >>
  rpt gen_tac >> strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
     strip_tac >> gvs[bind_def]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes /\
   ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
     value_has_type tv v /\ val_wf tv v /\
     type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
     type_memory_size tv < 2 ** 64 /\ type_memory_size tv + 64 < dimword (:256)` by
    metis_tac[] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
      ~is_word_type (post_value_type ce e) ==>
      type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
      type_memory_size tvt < 2 ** 64` by
    (`post_value_type ce e = expr_type e \/
      post_value_type ce e = lowered_value_type ce e` by
       (Cases_on `e` >> simp[post_value_type_def] >>
        rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
        simp[post_value_type_def, vyperASTTheory.expr_type_def] >>
        IF_CASES_TAC >> simp[]) >>
     metis_tac[expr_body_pre_copy_ok, optionTheory.SOME_11]) >>
  qpat_x_assum `!es_pre tvv v ee tv G tn r. _` (qspec_then `es` mp_tac) >>
  disch_then drule_all >> strip_tac >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  simp[bind_def] >>
  irule abi_args_read_result_suffix_ptr >> simp[] >>
  qexists `v` >> conj_tac >- gvs[] >>
  irule (SRULE [] abi_args_captured_cons_capacity_ptr) >> gvs[] >>
  qpat_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  gvs[] >> qpat_x_assum `!v es1 G1 tn1 t. _`
    (qspecl_then [`v`, `ee0 with gas_obs := []`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> conj_tac
  >- (qexists `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
  qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[materialize_owned_post_def, stmt_state_rel_gas_obs]
QED

Theorem abi_args_captured_rec_capacity_ptr:
  abi_args_ready ctx func ce cx Inv (e::args) /\ Inv es /\
  (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
  expr_vv_sim_ptr d ctx PG func ce cx (expr_type e) e es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  compile_abi_encode_args compile_expr ce args sm = (ops,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func ce cx es s0 /\ ghost_inv d ce cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~is_word_type (expr_type e) /\
  (!es_pre tvv v ee tv G tn r.
    expr_body_pre ce cx env e es_pre /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    (!tvt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME tvt /\
      ~is_word_type (post_value_type ce e) ==>
      type_memory_bytes ce (post_value_type ce e) = type_memory_size tvt /\
      type_memory_size tvt < 2 ** 64) /\
    fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
    stmt_state_rel ctx func ce cx es s0 /\ local_ptrs_reserved ce sa /\
    ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    vv_post ctx func ce cx e es sa mid s0 ee tvv vv r /\
    read_result cx tvv ee = (INL v,ee) /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64 /\
    type_memory_size tv + 64 < dimword (:256) /\
    ghost_inv d ce cx ee G tn r /\
    ptr_vv_ok cx (post_value_type ce e) tvv vv ee G tn r /\
    (!t' a. vv = StackValue t' a /\ ~is_word_type (post_value_type ce e) ==>
      ptr_buf_ok ce e a G r) /\
    (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G r) /\
    ghost_kept ce es sa G0 tn0 s0 G tn /\
    ~r.vs_halted /\ r.vs_current_bb = mid.cs_current_bb /\
    r.vs_inst_idx = LENGTH mid.cs_current_insts ==>
    ?H tm t. gas_path_ptr (cx_dead cx) 0 ctx func PG G tn r 0 H tm (OK t) /\
      materialize_owned_post ctx func ce cx e es sa mid sm s0 ee v op tv t /\
      ptr_val_ok cx (lowered_value_type ce e) v op H tm t /\
      ptr_buf_ok ce e op H t /\
      ghost_inv d ce cx ee H tm t /\ ghost_kept ce es sa G0 tn0 s0 H tm /\
      ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts) /\
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
  strip_tac >> drule_all abi_args_compile_captured_ptr_context >> strip_tac >>
  irule abi_args_captured_head_capacity_ptr >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all abi_args_success_ready_ptr >> simp[]) >>
  conj_tac >- metis_tac[expr_body_pre_vv_gas_admissible] >>
  qexists `env` >> simp[] >> conj_tac >- gvs[] >>
  rpt gen_tac >> strip_tac >>
      drule_all abi_args_success_ready_ptr >> strip_tac >>
      `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
        (gvs[ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
      qpat_x_assum `!es1 sa1 ops1 sb1 t G1 tn1. _` drule_all >> strip_tac >>
      dxrule gas_outcome_ptr_eval_evidence >> strip_tac >>
      irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> simp[] >>
      rpt gen_tac >> strip_tac >> gnvs[] >>
      qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >> strip_tac >>
      drule eval_exprs_preserves_scopes_dom >> simp[]
QED
