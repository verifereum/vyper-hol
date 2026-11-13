(* Captured argument composition; materialization is an explicit operational
   premise, discharged by the owned-materialization theory, not an S1 lift. *)
Theory abiEncTuplePtrCapturedHead
Ancestors
  abiEncTuplePtrCapturedPrefix abiEncTuplePtrArgsCompose
  abiEncTuplePtrArgsContext exprSimAbiEncodeArgsMaterializePath
  exprSimWordArgs vyperState abiEncodeArgsSim gasSummaryComposePtr

Theorem abi_args_captured_head_ptr:
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
  (!tvv v ee tv G tn r.
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
  qpat_x_assum `!tvv v ee tv G tn r. _` drule_all >> strip_tac >>
  irule gas_outcome_ptr_prefix >> goal_assum (drule_at Any) >>
  simp[bind_def] >>
  irule abi_args_read_result_suffix_ptr >> simp[] >>
  qexists `v` >> conj_tac >- gvs[] >>
  irule (SRULE [] abi_args_captured_cons_ptr) >> gvs[] >>
  qpat_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >>
  gvs[] >> qpat_x_assum `!v es1 G1 tn1 t. _`
    (qspecl_then [`v`, `ee0 with gas_obs := []`] mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> conj_tac
  >- (qexists `gas_explicit marks s0.vs_gas_readings` >> simp[]) >>
  qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[materialize_owned_post_def, stmt_state_rel_gas_obs]
QED
