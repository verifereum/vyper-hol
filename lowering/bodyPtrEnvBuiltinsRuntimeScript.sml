(* Final runtime assembly: ordinary runs identify endpoints, counted certificates
   supply the independently checked pointer path. *)
Theory bodyPtrEnvBuiltinsRuntime
Ancestors bodyPtrEnvBuiltinsRuntimeCompose bodyPtrEnvBuiltinsRuntimePost
  bodyPtrEnvBuiltinsRuntimeSemantics exprSimHash exprLoweringProps
  compileEnv loweringStateRelDefs bodyPtrDefs freshWrites wordArgsPtr finite_map venomState
  vyperTypeSystem emitHelper context bodyPtrEnvBuiltinsMask
  bodyPtrEnvBuiltinsSelectorCompile list loweringPosts

Theorem method_id_runtime_fixed_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ptr_val_ok cx (expr_type e) v arg G tn s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (arg,sm) /\
  compile_method_id_runtime (expr_type e) arg T sm = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct fn /\ ghost_inv d cenv cx es' G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sb fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t r G' tn'. run_inst_seq (emitted_insts sm sb) s = OK t /\
    builtin_result cx es'.accounts (BaseT (BytesT (Fixed 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Fixed 4))) MethodId [e])
      es sa sb s0 es' (Value r) (StackValue (BaseT (BytesT (Fixed 4))) op)
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 4))) r op G' tn' t /\
    ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es' sm G tn s G' tn'
Proof
  strip_tac >>
  drule_all method_id_runtime_counted_endpoint_post >> simp[] >> strip_tac >>
  drule hash_method_id_runtime_cut >> strip_tac >>
  drule_all hash_method_id_hash_cut >> strip_tac >> gvs[] >>
  drule method_id_typed_mask_counted >> simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`r`, `PG`, `D`] strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem method_id_mask_growth:
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (op,sb) ==>
  sh.cs_next_var <= sb.cs_next_var /\ sh.cs_next_id <= sb.cs_next_id /\
  (!x. op = Var x ==> not_fresh_at sb x)
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def, not_fresh_at_def] >>
  strip_tac >> gvs[] >> simp[]
QED

Theorem method_id_runtime_dynamic_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ptr_val_ok cx (expr_type e) v arg G tn s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (arg,sm) /\
  compile_method_id_runtime (expr_type e) arg F sm = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct fn /\ ghost_inv d cenv cx es' G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sb fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t r G' tn'. run_inst_seq (emitted_insts sm sb) s = OK t /\
    builtin_result cx es'.accounts (BaseT (BytesT (Dynamic 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post ctx fn cenv cx (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (LocatedValue (BaseT (BytesT (Dynamic 4)))
        <|ptr_location := LocMemory; ptr_operand := op|>)
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) r op G' tn' t /\
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]) op G' t /\
    ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es' sm G tn s G' tn'
Proof
  strip_tac >>
  drule_all method_id_runtime_counted_endpoint_post >> simp[] >> strip_tac >>
  drule hash_method_id_runtime_cut >> strip_tac >>
  drule_all hash_method_id_hash_cut >> strip_tac >> gvs[] >>
  drule_all hash_method_id_mask_cut >> strip_tac >>
  drule method_id_typed_mask_counted >> simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`ARB`, `PG`, `D`] strip_assume_tac) >>
  drule_all method_id_hash_grows >> strip_tac >>
  drule_all method_id_mask_growth >> strip_tac >>
  `sm.cs_next_var <= sp.cs_next_var /\ sm.cs_next_id <= sp.cs_next_id` by
    decide_tac >>
  `local_ptrs_reserved cenv sp` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sp x)` by
    metis_tac[not_fresh_at_mono] >>
  drule method_id_hash_typed_shape >> simp[] >> disch_then drule_all >> strip_tac >>
  drule_all method_id_mask_compile_code >> strip_tac >>
  drule_all selector_compile_code >> strip_tac >>
  `sp.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sp` by
    (qspecl_then [`sm`, `sm'`, `sp`] mp_tac emitted_insts_append >>
     simp[APPEND_ASSOC]) >>
  `emitted_insts sm sb = emitted_insts sm sp ++ emitted_insts sp sb` by
    (irule emitted_insts_append >> simp[]) >>
  `run_inst_seq (emitted_insts sp sb) t' = OK t` by
    metis_tac[run_inst_seq_append] >>
  `op_taint tn'' word = {}` by gvs[ptr_val_ok_def, is_word_type_def] >>
  drule_all method_id_selector_word_bytes >> strip_tac >>
  `stmt_state_rel ctx fn cenv cx es' s` by gvs[expr_post_def] >>
  gvs[] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) method_id_selector_append_counted >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `emit_void MSTORE [_;_] _ = _`)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspec_then `[e]` strip_assume_tac) >>
  gvs[] >> metis_tac[]
QED

Theorem method_id_runtime_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ptr_val_ok cx (expr_type e) v arg G tn s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (arg,sm) /\
  compile_method_id_runtime (expr_type e) arg fixed sm = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct fn /\ ghost_inv d cenv cx es' G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sb fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t r G' tn'. run_inst_seq (emitted_insts sm sb) s = OK t /\
    builtin_result cx es'.accounts
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post ctx fn cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
        <|ptr_location := LocMemory; ptr_operand := op|>)
      (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) r op G' tn' t /\
    (~fixed ==> ptr_buf_ok cenv
      (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]) op G' t) /\
    ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es' sm G tn s G' tn'
Proof
  Cases_on `fixed` >> simp[]
  >- (strip_tac >> drule_all method_id_runtime_fixed_counted >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]) >>
  strip_tac >> drule_all method_id_runtime_dynamic_counted >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED
