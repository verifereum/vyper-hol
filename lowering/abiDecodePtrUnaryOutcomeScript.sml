(* Unary composition whose continuation may carry a licensed exemption. *)
Theory abiDecodePtrUnaryOutcome
Ancestors
  abiDecodePtrExpr bodyPtrHashBuiltinsSuffix bodyPtrHashBuiltinsUnary
  bodyPtrDefs gasSummaryComposePtr fragGasPathPtr gasExemptCert
  exprSimHash exprSimSource exprSimDefs exprSimHypsDefs
  vyperState vyperInterpreter list

Theorem value_outcome_ptr_suffix:
  gas_outcome_ptr D tops (ctx,func) PG source (es,s0,G0,tn0)
    (\res ee G tn t. ?v:value. res = INL v /\ P v ee G tn t)
    (\res ee gt r. expr_exit res r) /\
  (!exc ee gt r. expr_exit (INR exc : value + exception) r ==>
    R (INR exc) ee gt r) /\
  (!gs v ee G tn t.
    source (es with gas_obs := gs) = (INL v,ee) /\ ee.gas_obs = [] /\
    P v ee G tn t /\ ~t.vs_halted ==>
    gas_outcome_ptr D tops (ctx,func) PG (k v) (ee,t,G,tn) Q R) ==>
  gas_outcome_ptr D tops (ctx,func) PG (bind source k) (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >>
      gvs[]
      >- (drule hash_marked_ptr_normal >> strip_tac >>
          qpat_x_assum `!gs v ee G tn t. _` drule >>
          simp[] >> disch_then drule_all >> strip_tac >>
          irule gas_outcome_ptr_bind_normal >>
          first_assum (irule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
          simp[] >> rpt strip_tac >>
          irule gas_exempt_cert_bind_value >> goal_assum (drule_at Any) >> simp[]) >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >>
      disj1_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
      metis_tac[gas_marked_exec_ptr_bind_exception]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj2_tac >>
  simp[ignore_bind_def, bind_assoc] >>
  metis_tac[gas_exempt_cert_error_value]
QED

Theorem type_builtin_unary_vv_sim_ptr_outcome:
  expr_body_pre cenv cx env e es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
  type_builtin_args_length_ok tb 1 /\
  (!sa sb vv. compile_expr cenv ty (TypeBuiltin ann tb typ [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!sa sm sb x vv s0 G0 tn0 gs v ee G tn s.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
    ee.gas_obs = [] /\
    expr_post ctx func cenv cx e es sa sm s0 ee v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn s /\
    ptr_val_ok cx (expr_type e) v x G tn s /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
        (\w. return (Value w))) (ee,s,G,tn)
      (\res ef G' tn' t. ?tv. res = INL tv /\
        vv_post ctx func cenv cx (TypeBuiltin ann tb typ [e]) es sa sb s0 ef tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv d cenv cx ef G' tn' t /\
        ptr_vv_ok cx (expr_type (TypeBuiltin ann tb typ [e])) tv vv ef G' tn' t /\
        (!t' op. vv = StackValue t' op /\
          ~is_word_type (expr_type (TypeBuiltin ann tb typ [e])) ==>
          ptr_buf_ok cenv (TypeBuiltin ann tb typ [e]) op G' t) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv (TypeBuiltin ann tb typ [e]) p.ptr_operand G' t) /\
        ghost_kept cenv es sa G0 tn0 s0 G' tn')
      (\res ef gt r. expr_exit res r)) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann tb typ [e]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_ptr_def] >> rpt strip_tac >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `eval_expr cx (TypeBuiltin ann tb typ [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
        (\w. return (Value w)))` by
    (irule eval_expr_unary_type_builtin_action >> simp[]) >>
  asm_rewrite_tac[] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule value_outcome_ptr_suffix >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >> metis_tac[hash_expr_exit_cast]) >>
  qexists_tac `\v ee G tn t.
    expr_post ctx func cenv cx e es sa sm s0 ee v x t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv d cenv cx ee G tn t /\
    ptr_val_ok cx (expr_type e) v x G tn t /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G t) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn` >>
  simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!sa sm sb x vv s0 G0 tn0 gs v ee G tn s. _` drule_all >> simp[]
QED
