(* SHA's continuation consumes source precompile outcomes, not a pure result. *)
Theory bodyPtrHashBuiltinsShaUnary
Ancestors
  bodyPtrHashBuiltinsUnary bodyPtrHashBuiltinsSuffix bodyPtrDefs exprSimHash
  exprSimSource exprSimHypsDefs exprSimDefs gasOutcome fragGasPathPtr
  gasStorage vyperStorageTrace vyperStorageFootprint gasContext vyperState vyperInterpreter list

Theorem hash_compile_typed_sha256_unary_vv_sim_ptr:
  expr_body_pre cenv cx env (Builtin ann Sha256 [e]) es /\
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
  expr_type e = BaseT bty /\
  (!sa sb vv. compile_expr cenv ty (Builtin ann Sha256 [e]) sa = (vv,sb) ==>
    ?x sm. lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
      code x sm = (vv,sb)) /\
  (!x. cs_appends (code x)) /\
  (!st0 sa sm sb x vv s0 G0 tn0 v gs ee G tn s.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    code x sm = (vv,sb) /\ fn_has_code sm sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    local_ptrs_reserved cenv sm /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at sa z) /\
    bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL v,ee) /\ ee.gas_obs = [] /\
    value_has_type (BaseTV bty) v /\ expr_sim_inv cenv cx env ee /\
    (?H. valid_horizon cx st0 H ee.storage_trace) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 ee v x s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts /\
    ghost_inv H d cenv cx ee G tn s /\
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn) /\
    local_ptrs_rel func cenv es.scopes s0 ==>
    ?marks. gas_summary_ptr_at (\H. cx_dead H cx) (ctx,func) PG cx st0 marks
      (\es'. case builtin_result cx es'.accounts ann Sha256 [expr_type e] [v] of
         INR exc => (INR exc,es')
       | INL w => (do precompile_call_success Sha256; return (Value w) od) es')
      (ee,s,G,tn)
      (\H res ef G' tn' t. ?tv. res = INL tv /\
        vv_post H ctx func cenv cx (Builtin ann Sha256 [e]) es sa sb s0 ef tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        ghost_inv H d cenv cx ef G' tn' t /\
        ptr_vv_ok cx (expr_type (Builtin ann Sha256 [e])) tv vv ef G' tn' t /\
        (!t' op. vv = StackValue t' op /\
           ~is_word_type (expr_type (Builtin ann Sha256 [e])) ==>
           ptr_buf_ok cenv (Builtin ann Sha256 [e]) op G' t) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok cenv (Builtin ann Sha256 [e]) p.ptr_operand G' t) /\
        ghost_kept cenv es sa G0 tn0 s0 G' tn')
      (\H res ef gt r. expr_exit res r)) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Builtin ann Sha256 [e]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_ptr_def] >> rpt strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gas_bad_storage_at_initial >> simp[evaluate_storage_trace_frame]) >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by
    (fs[storage_trace_domain_def] >> metis_tac[]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0` by metis_tac[] >>
  `local_ptrs_rel func cenv es.scopes s0` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `expr_body_pre cenv cx env e es` by
    (irule expr_body_pre_builtin_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
     gvs[expr_body_pre_def]) >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  rewrite_tac[eval_expr_sha256_action] >>
  `!w. storage_trace_frame
    (ignore_bind (precompile_call_success Sha256) (return (Value w)))` by
    simp[storage_trace_frame_ignore_bind, storage_trace_frame_precompile_call_success,
      storage_trace_frame_return] >>
  `!v. storage_trace_frame (\es'.
    case builtin_result cx es'.accounts ann Sha256 [expr_type e] [v] of
      INR exc => (INR exc,es')
    | INL w => (do precompile_call_success Sha256; return (Value w) od) es')` by
    (qpat_x_assum `!w. storage_trace_frame _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rewrite_tac[storage_trace_frame_def] >>
     rpt strip_tac >>
     Cases_on `builtin_result cx st.accounts ann Sha256 [expr_type e] [v]` >>
     pop_assum (fn th => simp_tac (srw_ss()) [th]) >>
     first_x_assum MATCH_ACCEPT_TAC) >>
  irule hash_expr_sim_ptr_suffix >>
  first_assum (irule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> metis_tac[hash_expr_exit_cast]) >>
  rpt strip_tac
  >~ [`storage_trace_frame _ (* g *)`]
  >- (qpat_x_assum `!v. storage_trace_frame _`
        (qspec_then `v` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env ee /\ value_has_type (BaseTV bty) v` by
    metis_tac[hash_operand_base_result] >>
  gvs[] >>
  qpat_x_assum `!st0 sa sm sb x vv s0 G0 tn0 v gs ee G tn s. _`
    (qspecl_then [`st0`, `sa`, `sm`, `sb`, `x`, `vv`, `s0`, `G0`, `tn0`,
      `v`, `gs`, `ee`, `G`, `tn`, `t`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED
