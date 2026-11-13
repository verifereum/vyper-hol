Theory bodyPtrTypeBuiltinsBytesWordSuccess
Ancestors bodyPtrTypeBuiltinsBytesWordInputs bodyPtrTypeBuiltinsBytesWordValueCounted
  bodyPtrTypeBuiltinsScalarContinuation bodyPtrTypeBuiltinsBytesWordTypes
  bodyPtrTypeBuiltinsBytesWordActual bodyPtrSignedConvertSourceTyping
  bodyPtrDefs exprLowering exprLoweringProps loweringPosts compileEnv venomState

Theorem bytes_word_success_post_counted:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst /\
  valid_conversion (expr_type e) dst /\ well_formed_type tenv dst /\
  ~((?b. dst = BaseT (IntT b)) \/ dst = BaseT DecimalT) /\
  lowered_value_type cenv e <> BaseT (BytesT (Dynamic 0)) /\
  lowered_value_type cenv e <> BaseT (StringT 0) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  compile_type_convert x (mk_convert_op (expr_type e) dst) sa = (out,sb) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  fn_has_code sa sb fn /\
  expr_post ctx fn cenv cx e es ca sa s0 ee v x s /\
  ptr_val_ok cx (expr_type e) v x G tn s /\ ptr_buf_ok cenv e x G s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es ca G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\ ca.cs_next_var <= sa.cs_next_var /\
  (!name p sz. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ expr_val_rel cx dst vout out t ==>
  ?H th.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H th
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    expr_post ctx fn cenv cx (TypeBuiltin dst Convert dst [e]) es ca sb s0
      (ee with gas_obs := []) vout out (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (t with vs_inst_idx := LENGTH sb.cs_current_insts).vs_current_bb = sb.cs_current_bb /\
    ghost_inv d cenv cx (ee with gas_obs := []) H th (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ptr_val_ok cx (post_value_type cenv (TypeBuiltin dst Convert dst [e])) vout out H th
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (~is_word_type (post_value_type cenv (TypeBuiltin dst Convert dst [e])) ==>
      ptr_buf_ok cenv (TypeBuiltin dst Convert dst [e]) out H (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ghost_kept cenv es ca G0 tn0 s0 H th
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    (drule_all body_source_lowered_nonzero_capacity >> simp[]) >>
  drule_all bytes_word_child_memory_inputs >> strip_tac >>
  qpat_x_assum `x = Var _` SUBST_ALL_TAC >>
  drule_all bytestring_scalar_unsigned_convert_op >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `not_fresh_at sa src` by simp[] >>
  (Q.SUBGOAL_THEN `?n. n <= 32 /\
    ((?bs. v = BytesV bs /\ n = LENGTH bs /\ tv <> BaseTV AddressT /\
       (!k. tv <> BaseTV (BytesT (Fixed k)))) \/
     (?str. v = StringV str /\ n = LENGTH str))`
    (qx_choose_then `n` (map_every assume_tac o CONJUNCTS))
    >- (drule_all bytes_word_source_length >> metis_tac[])) >>
  drule_all bytes_word_value_counted_success >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule_all bytes_word_unsigned_run_frame >> strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s` by fs[expr_post_def] >>
  `(t with vs_vars := s.vs_vars) = s` by
    (qpat_assum `t = s with vs_vars := _` (fn eq => once_rewrite_tac[eq]) >> simp[]) >>
  `s.vs_current_bb = sb.cs_current_bb` by
    (qpat_assum `t = s with vs_vars := _` mp_tac >>
     disch_then (mp_tac o AP_TERM ``\u:venom_state. u.vs_current_bb``) >> simp[]) >>
  `!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s` by metis_tac[] >>
  drule_all (SRULE [] (Q.INST [`j` |-> `LENGTH sb.cs_current_insts`]
    scalar_convert_success_post)) >> strip_tac >>
  qexistsl_tac [`H`,`th`] >> simp[]
QED
