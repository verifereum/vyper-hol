(* Unary type-builtin composition at the operand's physical post type. *)
Theory abiEncodeSinglePtrUnary
Ancestors
  bodyPtrHashBuiltinsSuffix bodyPtrHashBuiltinsUnary bodyPtrDefs
  exprSimHash exprSimSource exprSimHypsDefs exprSimDefs
  fragGasPathPtr vyperState vyperInterpreter list

Theorem type_builtin_unary_vv_sim_ptr_post_value:
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
    ptr_val_ok cx (post_value_type cenv e) v x G tn s /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e x G s) /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\
    stmt_state_rel ctx func cenv cx es s0 ==>
    ?marks. gas_summary_ptr_at (cx_dead cx) (ctx,func) PG marks
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
    (simp[Once evaluate_def] >>
     simp[type_check_def, assert_def, return_def, ignore_bind_def,
          Once evaluate_def, bind_assoc] >>
     simp[Once evaluate_def, assert_def, bind_def, return_def, FUN_EQ_THM]) >>
  asm_rewrite_tac[] >>
  irule hash_expr_sim_ptr_suffix >>
  first_assum (irule_at (Pat `expr_sim_ptr _ _ _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >> metis_tac[hash_expr_exit_cast]) >>
  rpt strip_tac >>
  qpat_x_assum `!sa sm sb x vv s0 G0 tn0 gs v ee G tn s. _` drule_all >> simp[]
QED
