(* Value/place packaging for the checked MethodId runtime suffix. *)
Theory bodyPtrEnvBuiltinsMethodRuntime
Ancestors bodyPtrEnvBuiltinsRuntime bodyPtrEnvBuiltinsRuntimeCompose
  bodyPtrEnvBuiltinsOperandFrame bodyPtrEnvBuiltinsBoundary
  exprSimHash exprLoweringProps exprSimWordArgs bodyPtrDefs
  loweringPosts wordArgsPtr freshWrites compileEnv context
  vyperInterpreter vyperValue vyperAST vyperState venomState
  entrySinkExtraction venomInst list finite_map

Theorem method_id_result_ptr_vv:
  ptr_val_ok cx (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) r op G tn s ==>
  ptr_vv_ok cx (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) (Value r)
    (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
     LocatedValue (BaseT (BytesT (Dynamic 4)))
       <|ptr_location := LocMemory; ptr_operand := op|>) es G tn s
Proof
  Cases_on `fixed` >>
  simp[ptr_vv_ok_def, read_result_def, return_def, ptr_val_ok_def,
       is_word_type_def, ptr_mem_ok_def]
QED

Theorem method_id_runtime_vv_suffix:
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
  stmt_state_rel ctx fn cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sb fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t r G' tn'.
    builtin_result cx es'.accounts
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post ctx fn cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
        <|ptr_location := LocMemory; ptr_operand := op|>) t /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ptr_vv_ok cx (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
        <|ptr_location := LocMemory; ptr_operand := op|>) es' G' tn' t /\
    (~fixed ==> ptr_buf_ok cenv
      (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [e]) op G' t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >> drule_all method_id_runtime_counted >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `wb_frame cenv es es' sa s0 s` by metis_tac[expr_post_frame] >>
  drule_all ghost_kept_wb_trans >> strip_tac >>
  drule_all method_id_typed_suffix_shape >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule (cj 2 run_inst_seq_preserves_entry_control) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `sb.cs_current_bb = sm.cs_current_bb` by gvs[same_blocks_def] >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`, `r`, `G'`, `tn'`] >>
  simp[] >> irule (SRULE [] method_id_result_ptr_vv) >> simp[]
QED
