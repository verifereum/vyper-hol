Theory bodyPtrBytestringBuiltinsUnary
Ancestors
  bodyPtrBytestringBuiltinsInterfaces exprSimSource gasSummaryComposePtr
  gasExemptCert exprSimHash stmtSimProps bodyPtrBytestringBuiltinsPrefix
  vyperInterpreter
Libs monadsyntax

Theorem unary_builtin_operand_sim_ptr:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  body_exprs_ptr_ok cx [e] /\
  expr_type e <> BaseT (BytesT (Dynamic 24576)) ==>
  expr_sim_ptr d ctx PG func cenv cx cty e es
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_typed_arg >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
     qexistsl_tac [`ann`, `[e]`, `bt`, `es`] >> simp[]) >>
  drule body_exprs_ptr_head >>
  simp[bodyPtrPredsTheory.body_expr_ptr_ok_def] >>
  metis_tac[]
QED

Theorem gas_outcome_ptr_value_bind:
  gas_outcome_ptr D tops (ctx, func) PG
    (source : evaluation_state -> value evaluation_result)
    (es, s0, G0, tn0) P E /\
  (!res ee G tn t. P res ee G tn t ==>
    ?v. res = INL v /\
      gas_outcome_ptr D tops (ctx, func) PG (next v) (ee, t, G, tn) Q R) /\
  (!res ee gt r. E res ee gt r ==>
    ?exc. res = INR exc /\ R (INR exc) ee gt r) ==>
  gas_outcome_ptr D tops (ctx, func) PG (bind source next)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >> irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >> irule gas_outcome_ptr_conseq >>
  qexistsl_tac [`P`, `E`] >> simp[]
QED

Theorem expr_sim_ptr_suffix:
  expr_sim_ptr d ctx PG func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op, sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee gt r. expr_exit (INR exc : value + exception) r ==>
    R (INR exc) ee gt r) /\
  (!v ee G tn t.
    expr_post ctx func cenv cx e es sa sm s0 ee v op t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
      (k v) (ee, t, G, tn) Q R) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx, func) PG
    (bind (bind (eval_expr cx e) (read_result cx)) k)
    (es, s0, G0, tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.expr_sim_ptr_def]) >>
  disch_then drule_all >> strip_tac >>
  drule forced_operand_outcome_scopes >> disch_tac >>
  irule gas_outcome_ptr_value_bind >>
  first_assum (irule_at (Pat `gas_outcome_ptr _ _ _ _ _ _ _ _`)) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_INL] >> metis_tac[]) >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[exprSimDefsTheory.expr_exit_INL] >> metis_tac[]
QED

Theorem compile_unary_builtin_rel_vv_sim_ptr:
  expr_body_pre cenv cx env (Builtin ann bt [e]) es /\
  expr_sim_ptr d ctx PG func cenv cx cty e es /\
  ~precompile_builtin bt /\ bt <> Len /\ builtin_args_length_ok bt 1 /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann bt [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv cty e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 G0 tn0 v ee G tn t.
    lower_value compile_expr cenv cty e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\
    ~cenv.ce_is_ctor /\
    stmt_state_rel ctx func cenv cx es s0 /\
    ghost_inv d cenv cx es G0 tn0 s0 /\
    expr_post ctx func cenv cx e es sa sm s0 ee v x t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn t /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (\vst. ((case builtin_result cx vst.accounts ann bt [expr_type e] [v] of
         INL w => INL (Value w) | INR exc => INR exc), vst))
      (ee,t,G,tn)
      (\res ef Gf tnf u. ?tv. res = INL tv /\
        vv_post ctx func cenv cx (Builtin ann bt [e]) es sa sb s0 ef tv vv u /\
        u.vs_current_bb = sb.cs_current_bb /\
        u.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv d cenv cx ef Gf tnf u /\
        ptr_vv_ok cx (expr_type (Builtin ann bt [e])) tv vv ef Gf tnf u /\
        (!t' op. vv = StackValue t' op /\
          ~is_word_type (expr_type (Builtin ann bt [e])) ==>
          ptr_buf_ok cenv (Builtin ann bt [e]) op Gf u) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv (Builtin ann bt [e]) p.ptr_operand Gf u) /\
        ghost_kept cenv es sa G0 tn0 s0 Gf tnf)
      (\res ef gt r. expr_exit res r)) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Builtin ann bt [e]) es
Proof
  strip_tac >> rewrite_tac[bodyPtrDefsTheory.expr_vv_sim_ptr_def] >>
  rpt strip_tac >>
  `!n. bt <> Slice n` by
    (rpt strip_tac >> gvs[vyperContextTheory.builtin_args_length_ok_def]) >>
  `expr_body_pre cenv cx env e es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then irule >> gvs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  drule_all eval_expr_unary_builtin_action >> disch_then (fn th => rewrite_tac[th]) >>
  irule expr_sim_ptr_suffix >>
  first_assum (irule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[expr_exit_INR_type]
QED
