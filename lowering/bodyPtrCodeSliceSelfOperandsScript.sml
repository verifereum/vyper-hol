Theory bodyPtrCodeSliceSelfOperands
Ancestors
  bodyPtrDefs wordArgsPtr typedWordArgsSimPtr compileEnv ptrDiscipline
  loweringPosts exprSimSliceOrdinaryContinue gasSummaryComposePtr
  gasOutcomeMarkedPtr typedWordArgsReadyPtr exprSimPrecompiles exprSimCalldataSlice
  exprSimSource fragExec exprLoweringProps exprSimWordArgs

(* Preserve all three observations needed by a later checked copy. *)
Theorem code_slice_word_operand_frame:
  wb_frame cenv es ee sa s0 s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w /\
  op_taint tn op = op_taint tn0 op /\ op_prov G op = op_prov G0 op
Proof
  strip_tac >> drule_all word_operand_frame >> strip_tac >> simp[] >>
  Cases_on `op` >> gvs[op_prov_def, ghost_kept_def] >> metis_tac[]
QED

Theorem code_slice_uint_read_ptr_post:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx e es sa sb s ee v op t /\
  ptr_val_ok cx (expr_type e) v op G tn t ==>
  expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  ?i. v = IntV (&i) /\ i < dimword (:256) /\ eval_operand op t = SOME (n2w i)
Proof
  strip_tac >> drule_all slice_uint_read_post >>
  gvs[ptr_val_ok_def, is_word_type_def]
QED

Theorem code_slice_uint_marked_ptr_post:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) mid G tn (OK t) /\
  expr_post ctx func cenv cx e es sa sb s0 (mid with gas_obs := []) v op t /\
  ptr_val_ok cx (expr_type e) v op G tn t ==>
  expr_sim_inv cenv cx env (mid with gas_obs := []) /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  ?i. v = IntV (&i) /\ i < dimword (:256) /\ eval_operand op t = SOME (n2w i)
Proof
  strip_tac >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all code_slice_uint_read_ptr_post >> simp[]
QED

(* Extra facts are inside the explicit success post, so matching the
   outcome also fixes the compiler endpoints and the returned operand. *)
Theorem code_slice_uint_outcome_ptr:
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?v. rr = INL v /\
      expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
      ptr_val_ok cx (expr_type e) v op G tn t /\ H v ee G tn t) R ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?i. rr = INL (IntV (&i)) /\ i < dimword (:256) /\
      expr_post ctx func cenv cx e es sa sb s0 ee (IntV (&i)) op t /\
      ptr_val_ok cx (expr_type e) (IntV (&i)) op G tn t /\
      H (IntV (&i)) ee G tn t /\
      expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      eval_operand op t = SOME (n2w i) /\
      op_taint tn op = {} /\ op_prov G op = NONE) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> rpt strip_tac >> BETA_TAC >>
  qpat_x_assum `(\rr ee G tn t. _) _ _ _ _ _`
    (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `rr = INL v` SUBST_ALL_TAC >>
  drule_all code_slice_uint_marked_ptr_post >> strip_tac >>
  qexists_tac `i` >> gvs[]
QED

Theorem code_slice_uint_head_outcome_ptr:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  expr_body_pre cenv cx env e es /\ expr_type e = BaseT (UintT 256) /\
  lower_value compile_expr cenv (arg_ty e) e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?i. rr = INL (IntV (&i)) /\ i < dimword (:256) /\
      expr_post ctx func cenv cx e es sa sb s0 ee (IntV (&i)) op t /\
      ptr_val_ok cx (expr_type e) (IntV (&i)) op G tn t /\
      (~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv d cenv cx ee G tn t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
       Inv ee /\ typed_args_ready ctx func cenv cx arg_ty Inv args /\
       ptr_args_ready d ctx PG func cenv cx arg_ty Inv args) /\
      expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      eval_operand op t = SOME (n2w i) /\ op_taint tn op = {} /\ op_prov G op = NONE)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  drule_all ptr_args_ready_head >> rewrite_tac[expr_sim_ptr_def] >>
  disch_then (qspecl_then [`sa`,`sb`,`op`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac
  >- (simp[] >> drule_all typed_args_ptr_head_admissible >> simp[SF ETA_ss]) >>
  strip_tac >>
  drule_all (typed_args_ptr_head_outcome_facts |>
    SIMP_RULE (srw_ss()) [SF ETA_ss]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >> disch_tac >>
  ho_match_mp_tac code_slice_uint_outcome_ptr >> simp[] >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> fs[] >> metis_tac[]) >> simp[]
QED

(* Rebase a located-value continuation across an operand prefix. *)
Theorem code_slice_vv_post_ptr_rebase:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  wb_frame cenv es es1 sa s0 t /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  vv_post ctx func cenv cx e es1 sm sb t es2 tv vv u /\
  ghost_kept cenv es1 sm G1 tn1 t G tn ==>
  vv_post ctx func cenv cx e es sa sb s0 es2 tv vv u /\
  ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >> conj_tac
  >- metis_tac[vv_post_prefix_frame] >>
  metis_tac[ghost_kept_wb_trans]
QED

Theorem code_slice_two_uint_outcome_ptr:
  typed_args_ready ctx func cenv cx arg_ty Inv [start;len] /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv [start;len] /\ Inv es /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  expr_body_pre cenv cx env start es /\
  (!ee. Inv ee ==> expr_body_pre cenv cx env len ee) /\
  expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256) /\
  lower_value compile_expr cenv (arg_ty start) start sa = (sop,sm) /\
  lower_value compile_expr cenv (arg_ty len) len sm = (lop,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (bind (eval_expr cx start) (read_result cx)) (return ()))
      (es,s0) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx start) (read_result cx)) (\v.
        ignore_bind (bind (bind (eval_expr cx len) (read_result cx)) (next v)) (return ())))
      (es,s0) marks (err,ee) (leaf,fstate)) /\
  (!left v mid t right err ee leaf fstate.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx start) (read_result cx))
      (es,s0) left (INL v) mid (OK t) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (bind (bind (eval_expr cx len) (read_result cx)) (next v)) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx start) (read_result cx)) (\v.
        ignore_bind (bind (bind (eval_expr cx len) (read_result cx)) (next v)) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,fstate)) /\
  (!v es1 t marks err ee leaf fstate.
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (ignore_bind (bind (eval_expr cx len) (read_result cx)) (return ()))
      (es1,t) marks (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx len) (read_result cx)) (\w. ignore_bind (next v w) (return ())))
      (es1,t) marks (err,ee) (leaf,fstate)) /\
  (!v es1 t left w mid u right err ee leaf fstate.
    gas_marked_exec F (ctx,func) (bind (eval_expr cx len) (read_result cx))
      (es1,t) left (INL w) mid (OK u) /\
    gas_exempt_cert F (cx_tops cx) (ctx,func) (ignore_bind (next v w) (return ()))
      (mid with gas_obs := [],u) right (err,ee) (leaf,fstate) ==>
    gas_exempt_cert F (cx_tops cx) (ctx,func)
      (bind (bind (eval_expr cx len) (read_result cx)) (\w. ignore_bind (next v w) (return ())))
      (es1,t) (left ++ right) (err,ee) (leaf,fstate)) /\
  (!res ee gt r. expr_exit (res : value + exception) r ==>
     ?exc. res = INR exc /\ R (INR exc) ee gt r) /\
  (!i k ee G tn t.
    i < dimword (:256) /\ k < dimword (:256) /\
    eval_operand sop t = SOME (n2w i) /\ eval_operand lop t = SOME (n2w k) /\
    op_taint tn sop = {} /\ op_taint tn lop = {} /\
    op_prov G sop = NONE /\ op_prov G lop = NONE /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func cenv cx ee t /\ ghost_inv d cenv cx ee G tn t /\
    expr_sim_inv cenv cx env ee /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    wb_frame cenv es ee sa s0 t /\ ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (next (IntV (&i)) (IntV (&k))) (ee,t,G,tn) Q R) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (bind (eval_expr cx start) (read_result cx)) (\v.
       bind (bind (eval_expr cx len) (read_result cx)) (next v)))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  `expr_body_pre cenv cx env len es` by metis_tac[] >>
  `is_word_type (expr_type start) /\ is_word_type (expr_type len)` by
    simp[is_word_type_def] >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\
   (!z. sop = Var z ==> not_fresh_at sm z) /\ (!l. sop <> Label l)` by
    metis_tac[expr_body_pre_lower_value_word_shape] >>
  `cs_extends sm sb` by metis_tac[expr_body_pre_lower_value_word_shape] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all code_slice_uint_head_outcome_ptr >> disch_tac >>
  irule gas_outcome_ptr_bind >> BETA_TAC >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  reverse conj_tac >- (BETA_TAC >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `expr_body_pre cenv cx env len ee` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx ee t` by metis_tac[expr_post_def] >>
  drule_all code_slice_uint_head_outcome_ptr >> disch_tac >>
  irule gas_outcome_ptr_bind >> BETA_TAC >> simp[] >>
  conj_tac >- metis_tac[] >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  reverse conj_tac >- (BETA_TAC >> metis_tac[]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >> gvs[] >>
  `wb_frame cenv ee ee' sm t t'` by metis_tac[expr_post_frame] >>
  `eval_operand sop t' = SOME (n2w i) /\ op_taint tn' sop = {} /\
   op_prov G' sop = NONE` by
    metis_tac[code_slice_word_operand_frame] >>
  `wb_frame cenv es ee' sa s0 t'` by
    metis_tac[expr_post_frame, wb_frame_trans] >>
  `wb_frame cenv es ee sa s0 t` by metis_tac[expr_post_frame] >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    metis_tac[ghost_kept_wb_trans] >>
  `stmt_state_rel ctx func cenv cx ee' t'` by metis_tac[expr_post_def] >>
  first_x_assum irule >> simp[]
QED
