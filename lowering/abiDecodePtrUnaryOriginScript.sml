(* Unary composition retaining the concrete operand prefix for exemptions. *)
Theory abiDecodePtrUnaryOrigin
Ancestors
  abiDecodePtrExpr bodyPtrHashBuiltinsSuffix bodyPtrHashBuiltinsUnary
  bodyPtrDefs gasSummaryComposePtr fragGasPathPtr gasExemptCert
  gasExemptOrigin gasNormalPrefix exprSimHash exprSimSource exprSimDefs
  exprSimHypsDefs vyperState vyperInterpreter list

Theorem type_builtin_unary_vv_sim_ptr_origin:
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
    (?marks. gas_summary_ptr_at (cx_dead cx) (ctx,func) PG marks
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
      (\res ef gt r. expr_exit res r)) \/
    (?err. evaluate_type_builtin cx tb typ [expr_type e] [v] = INR err /\
      ((tb = Convert /\ err = RuntimeError "convert empty bytes to signed") \/
       (?unwrap. tb = AbiDecode unwrap /\ err = RuntimeError "abi_decode invalid" /\
         ?target_ty. occurs_abi_decode_target target_ty (cx_tops cx) /\
           is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target_ty))))) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann tb typ [e]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_ptr_def] >> rpt strip_tac >>
  qpat_x_assum `!sa sb vv. _` drule >> strip_tac >>
  `cs_appends (code x)` by simp[] >>
  drule_all hash_unary_suffix_cut >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `x`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >>
      gvs[]
      >- (drule hash_marked_ptr_normal >> strip_tac >>
          qpat_x_assum `!sa sm sb x vv s0 G0 tn0 gs v ee G tn s. _` drule >>
          simp[] >> disch_then (drule_at (Pat `bind _ _ _ = _`)) >>
          simp[] >> disch_then drule_all >> strip_tac
          >- suspend "counted"
          >> suspend "origin")
      >> suspend "exception")
  >> suspend "operand_exempt"
QED

Resume type_builtin_unary_vv_sim_ptr_origin[counted]:
  qexists_tac `marks ++ marks'` >> disj1_tac >>
  `eval_expr cx (TypeBuiltin ann tb typ [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
        (\w. return (Value w)))` by
    (irule eval_expr_unary_type_builtin_action >> simp[]) >>
  asm_rewrite_tac[] >> irule gas_summary_ptr_at_bind_normal >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume type_builtin_unary_vv_sim_ptr_origin[origin]:
  markerLib.RESUME_TAC >> qexists_tac `marks` >> disj2_tac >>
  irule_at Any gas_exempt_cert_origin >>
  rewrite_tac[gas_exempt_origin_def] >>
  first_assum (irule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  simp[] >> qexistsl_tac [`v`, `t`, `sm`, `x`, `es_end`, `cx`] >>
  gvs[gas_value_prefix_def] >>
  metis_tac[gas_marked_exec_ptr_exec]
QED
Resume type_builtin_unary_vv_sim_ptr_origin[exception]:
  Cases_on `res` >> gvs[expr_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  `eval_expr cx (TypeBuiltin ann tb typ [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
        (\w. return (Value w)))` by
    (irule eval_expr_unary_type_builtin_action >> simp[]) >>
  asm_rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR y`, `es_end`, `G`, `tn`, `r`] >>
  conj_tac >- (irule gas_marked_exec_ptr_bind_exception >> goal_assum (drule_at Any)) >>
  simp[] >> metis_tac[hash_expr_exit_cast]
QED
Resume type_builtin_unary_vv_sim_ptr_origin[operand_exempt]:
  qexists_tac `marks` >> disj2_tac >>
  `eval_expr cx (TypeBuiltin ann tb typ [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (lift_sum (evaluate_type_builtin cx tb typ [expr_type e] [v]))
        (\w. return (Value w)))` by
    (irule eval_expr_unary_type_builtin_action >> simp[]) >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  asm_rewrite_tac[] >> rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_error_value >> asm_rewrite_tac[ignore_bind_def]
QED
Finalise type_builtin_unary_vv_sim_ptr_origin
