(* Observation bookkeeping for applying a Convert continuation to a marked child. *)
Theory bodyPtrTypeBuiltinsConvertMarked
Ancestors bodyPtrTypeBuiltinsConvert gasSummaryComposePtr fragGasPathPtr
  fragGasSeqPtr exprSimSource exprSimWordArgs exprSimIfExp
  bodyPtrDefs loweringPosts vyperState vyperAST

Theorem expr_post_initial_gas_obs[simp]:
  expr_post ctx func cenv cx e (es with gas_obs := gs) sa sb s0 ee v op t =
  expr_post ctx func cenv cx e es sa sb s0 ee v op t
Proof
  simp[expr_post_def, locals_kept_def]
QED

Theorem ghost_kept_initial_gas_obs[simp]:
  ghost_kept cenv (es with gas_obs := gs) sa G0 tn0 s0 G tn =
  ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  simp[ghost_kept_def]
QED

Theorem marked_operand_success:
  expr_body_pre cenv cx env e es /\
  gas_marked_exec_ptr D (ctx,func) PG
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) mid G tn (OK t) ==>
  ~t.vs_halted /\
  (do r <- eval_expr cx e; read_result cx r od)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := []) /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  strip_tac >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_marked_exec_ptr_def]) >>
  `~t.vs_halted` by metis_tac[gas_path_ptr_ok_not_halted] >>
  first_x_assum (qspec_then `[]` assume_tac) >> fs[SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] ifexp_body_pre_read_typed) >>
  metis_tac[expr_body_pre_gas_obs]
QED

Theorem convert_marked_normal_continuation:
  expr_post ctx func cenv cx e es sa sm s0 (mid with gas_obs := []) v x t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert typ [e]) es /\
  ~(is_bytestring_type (expr_type e) /\
    ((?n. typ = BaseT (IntT n)) \/ typ = BaseT DecimalT)) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_type_builtin_dispatch_body compile_expr cenv ann ty Convert typ [e] sa =
    (StackValue ann op,sb) /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    marks (INL v) mid G tn (OK t) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  ptr_val_ok cx (expr_type e) v x G tn t /\
  (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e x G t) /\
  ghost_inv d cenv cx (mid with gas_obs := []) G tn t /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  body_inv tops ctx cenv cx /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\vs. (convert_result cx (expr_type e) typ v,vs))
    (mid with gas_obs := [],t,G,tn)
    (\res fin H th ss. ?w. res = INL w /\
      expr_post ctx func cenv cx (TypeBuiltin ann Convert typ [e])
        es sa sb s0 fin w op ss /\
      ss.vs_current_bb = sb.cs_current_bb /\ ss.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx fin H th ss /\ ptr_val_ok cx typ w op H th ss /\
      (~is_word_type typ ==> ptr_buf_ok cenv (TypeBuiltin ann Convert typ [e]) op H ss) /\
      ghost_kept cenv es sa G0 tn0 s0 H th)
    (\res fin gt out. exprSimDefs$expr_exit res out)
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e es` by
    (drule exprSimConvertTheory.expr_body_pre_convert >> simp[]) >>
  drule_all marked_operand_success >> strip_tac >>
  rule_assum_tac (SRULE [SF ETA_ss]) >>
  drule_at (Pat `vyperState$bind _ _ _ = _`)
    (SRULE [SF ETA_ss] convert_normal_continuation) >>
  simp[expr_post_initial_gas_obs, ghost_kept_initial_gas_obs,
       expr_body_pre_gas_obs, stmt_state_rel_gas_obs] >>
  disch_then drule_all >>
  disch_then (qspec_then `PG` assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> simp[SF ETA_ss]
QED
