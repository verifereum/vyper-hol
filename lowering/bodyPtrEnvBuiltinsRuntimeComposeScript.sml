(* Composition keeps raw semantic endpoints separate from path cursors. *)
Theory bodyPtrEnvBuiltinsRuntimeCompose
Ancestors bodyPtrEnvBuiltinsHashTyped bodyPtrEnvBuiltinsMask
  bodyPtrEnvBuiltinsSelectorCompile bodyPtrEnvBuiltinsScalar
  fragGasPathPtr fragExec instIdxIndep exprSimHash exprLoweringProps
  compileEnv venomState venomInst words list bodyPtrDefs vyperTypeSystem
  wordArgsPtr loweringPosts finite_map bodyPtrEnvBuiltinsRuntimeSemantics freshWrites

Theorem ghost_kept_inst_idx[simp]:
  ghost_kept cenv es sa G0 tn0 (s with vs_inst_idx := k) G tn <=>
  ghost_kept cenv es sa G0 tn0 s G tn
Proof
  simp[ghost_kept_def, local_region_def, lookup_var_def]
QED

Theorem method_id_mask_append_counted:
  gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 G tn
    (OK (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
  emit_op SHR [Lit 224w; hash] sa = (sel,sm) /\
  emit_op SHL [Lit 224w; sel] sm = (op,sb) /\
  op_taint tn hash = {} /\ eval_operand hash s = SOME w /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  ghost_kept cenv es0 sf Gf tnf sf0 G tn /\ local_ptrs_reserved cenv sf /\
  (!x. not_fresh_at sf x ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sf x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 4))) result op G' tn' t /\
    ghost_inv d cenv cx es G' tn' t /\
    ghost_kept cenv es0 sf Gf tnf sf0 G' tn'
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule_all method_id_mask_compile_code >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb)
     (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
     OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_at (Pat `run_inst_seq _ _ = _`) method_id_mask_compile_counted >>
  disch_then (drule_all o SRULE []) >> simp[] >>
  disch_then (qspecl_then [`result`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem method_id_hash_mask_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ptr_val_ok cx (expr_type e) v arg G tn s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  compile_method_id_hash (expr_type e) arg sm = (hash,sh) /\
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct fn /\ ghost_inv d cenv cx es' G tn s /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sh /\
  (!x. not_fresh_at sm x ==> not_fresh_at sh x) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sh fn /\ fn_has_code sh sb fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sh) s = OK t /\
  eval_operand hash t = SOME w /\ ~t.vs_halted /\
  t.vs_current_bb = sh.cs_current_bb /\
  run_inst_seq (emitted_insts sh sb) t = OK u ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 4))) result op G' tn' u /\
    ghost_inv d cenv cx es' G' tn' u /\ ghost_kept cenv es' sm G tn s G' tn'
Proof
  strip_tac >>
  drule_at (Pat `compile_method_id_hash _ _ _ = _`) method_id_hash_typed_counted >>
  disch_then drule_all >>
  disch_then (qspecl_then [`ARB`, `PG`, `D`] strip_assume_tac) >>
  `op_taint tn' hash = {}` by
    gvs[ptr_val_ok_def, is_word_type_def] >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)
    method_id_mask_append_counted >>
  disch_then drule_all >> simp[]
QED

Theorem method_id_selector_append_counted:
  gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 G tn
    (OK (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sn = (data,sp) /\
  emit_void MSTORE [data; value] sp = ((),sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  fn_inst_ids_distinct fn /\ ~ctx_has_dalloca ctx /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand value s = SOME w /\ op_taint tn value = {} /\
  LENGTH bs = 4 /\ TAKE 4 (word_to_bytes w T) = bs /\
  ~s.vs_halted /\ fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  stmt_state_rel ctx fn cenv cx es0 sf0 /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\ wb_frame cenv es0 sf sf0 s /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
  ghost_kept cenv es0 sf Gf tnf sf0 G tn ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es0 sf Gf tnf sf0 G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) buf.buf_operand G' tn' t /\
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args) buf.buf_operand G' t
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (drule_all selector_compile_code >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb)
     (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
     OK (t with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  drule_at (Pat `run_inst_seq _ _ = _`) selector_compile_counted >>
  disch_then (drule_all o SRULE [stmt_state_rel_inst_idx]) >> simp[] >>
  disch_then (qspecl_then [`args`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  drule_all ghost_kept_wb_trans >> simp[]
QED

Theorem method_id_typed_mask_counted:
  expr_post ctx fn cenv cx e es sa sm s0 es' v arg s /\
  ptr_val_ok cx (expr_type e) v arg G tn s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (arg,sm) /\
  compile_method_id_hash (expr_type e) arg sm = (hash,sh) /\
  emit_op SHR [Lit 224w; hash] sh = (sel,sn) /\
  emit_op SHL [Lit 224w; sel] sn = (op,sb) /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  fn_inst_ids_distinct fn /\ ghost_inv d cenv cx es' G tn s /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ fn_has_code sm sh fn /\ fn_has_code sh sb fn /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t bs G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_val_ok cx (BaseT (BytesT (Fixed 4))) result op G' tn' t /\
    ghost_inv d cenv cx es' G' tn' t /\ ghost_kept cenv es' sm G tn s G' tn' /\
    stmt_state_rel ctx fn cenv cx es' t /\ wb_frame cenv es' sm s t /\
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ LENGTH bs = 4 /\
    eval_operand op t = SOME
      (typed_val_to_w256 (BaseTV (BytesT (Fixed 4))) (BytesV bs)) /\
    (!ann. builtin_result cx es'.accounts ann MethodId [expr_type e] [v] = INL (BytesV bs))
Proof
  strip_tac >> drule_all method_id_hash_mask_semantics >> strip_tac >>
  drule_all method_id_hash_grows >> strip_tac >>
  `local_ptrs_reserved cenv sh` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sh x` by
    metis_tac[not_fresh_at_mono] >>
  drule_at (Pat `compile_method_id_hash _ _ _ = _`) method_id_hash_mask_counted >>
  disch_then drule_all >>
  disch_then (qspecl_then [`result`, `PG`, `D`] strip_assume_tac) >>
  `~t.vs_halted /\ t.vs_current_bb = sh.cs_current_bb` by
    gvs[venom_state_component_equality] >>
  `sb.cs_current_bb = sh.cs_current_bb` by
    (drule_all method_id_mask_compile_code >> strip_tac >> simp[]) >>
  qexistsl_tac [`t`, `TAKE 4 bs`, `G'`, `tn'`] >> simp[LENGTH_TAKE_EQ]
QED
