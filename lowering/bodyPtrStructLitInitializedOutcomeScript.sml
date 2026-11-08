Theory bodyPtrStructLitInitializedOutcome
Ancestors bodyPtrStructLitInitializedMemoryCompose bodyPtrStructLitForcedMemoryOutcome
  exprSimMemorySource exprSimSource exprSimAggregateSource exprSimHypsDefs
  gasSummaryComposePtr fragGasPathPtr fragGasSeqPtr bodyPtrDefs exprSimDefs
  exprLowering loweringPosts venomState compileEnv finite_map words

Theorem structlit_first_memory_word_initialized_outcome:
  N = SUM (MAP (SND o SND)
    (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid))) /\
  expr_body_pre ce cx env (StructLit ann nsid ((fname,e)::rest)) es /\
  is_word_type (expr_type e) /\ is_word_type cty /\ is_word_type fty /\
  compile_expr ce ty (StructLit ann nsid ((fname,e)::rest)) sa = (out,sd) /\
  compile_alloc_buffer N sa = (buf,sb) /\ buf.buf_operand = Var root /\
  compile_expr ce (expr_type e) e sb = (LocatedValue cty q,sc) /\
  q.ptr_location = LocMemory /\
  emit_op ADD [buf.buf_operand; Lit 0w] sc = (Var dst,sm) /\
  unwrap_value ce (LocatedValue cty q) sm = (Var load,su) /\
  ALOOKUP (get_struct_fields ce.ce_struct_fields (nsid_to_string nsid)) fname =
    SOME (fty,sz) /\
  compile_store_memory ce (Var load) (Var dst) fty (lowered_value_type ce e)
    su = ((),sv) /\ fn_has_code sa sd fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  not_fresh_at sb root /\ ptr_covers G0 tn0 root t N /\
  eval_operand buf.buf_operand t = SOME addrw /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n addrw,N) /\
  ~ctx_has_dalloca ctx /\
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (eval_expr cx e) (es,t,G0,tn0)
    (\res ee G tn s.
      (?tv. res = INL tv /\
        vv_post ctx fn ce cx e es sb sc t ee tv (LocatedValue cty q) s /\
        s.vs_current_bb = sc.cs_current_bb /\
        s.vs_inst_idx = LENGTH sc.cs_current_insts /\
        ghost_inv d ce cx ee G tn s /\
        ptr_vv_ok cx (expr_type e) tv (LocatedValue cty q) ee G tn s /\
        (!ty' op. LocatedValue cty q = StackValue ty' op /\
          ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) /\
        (!ty' q'. LocatedValue cty q = LocatedValue ty' q' /\
          q'.ptr_location = LocMemory ==> ptr_buf_ok ce e q'.ptr_operand G s) /\
        ghost_kept ce es sb G0 tn0 t G tn) /\
      (!tv. res = INL tv ==>
        ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
          (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v)))
    (\res ee gt r. expr_exit res r) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
    (bind (eval_expr cx e) (read_result cx)) (es,t,G0,tn0)
    (\res ee Gf tnf sf. ?tv s G tn v w.
      res = INL v /\ read_result cx tv ee = (INL v,ee) /\
      ((?tv'. INL tv = INL tv' /\
        vv_post ctx fn ce cx e es sb sc t ee tv' (LocatedValue cty q) s /\
        s.vs_current_bb = sc.cs_current_bb /\
        s.vs_inst_idx = LENGTH sc.cs_current_insts /\
        ghost_inv d ce cx ee G tn s /\
        ptr_vv_ok cx (expr_type e) tv' (LocatedValue cty q) ee G tn s /\
        (!ty' op. LocatedValue cty q = StackValue ty' op /\
          ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) /\
        (!ty' q'. LocatedValue cty q = LocatedValue ty' q' /\
          q'.ptr_location = LocMemory ==> ptr_buf_ok ce e q'.ptr_operand G s) /\
        ghost_kept ce es sb G0 tn0 t G tn) /\
      (!tv'. INL tv = INL tv' ==>
        ?tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
          eval_result_typed (env,cx,ee) tv' (Type (expr_type e)) /\
          (!v. read_result cx tv' ee = (INL v,ee) ==> value_has_type tvt v))) /\
      gas_path_ptr (cx_dead cx) 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
      ghost_kept ce es sb G0 tn0 t Gf tnf /\
      stmt_state_rel ctx fn ce cx ee sf /\ ghost_inv d ce cx ee Gf tnf sf /\
      sf.vs_current_bb = sv.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sv.cs_current_insts /\
      (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
        w = typed_val_to_w256 tvt v) /\
      sf.vs_memory = (mstore (w2n addrw) w s).vs_memory /\
      mload (w2n addrw) sf = w /\ sf.vs_allocas = s.vs_allocas /\
      (!x. x <> dst /\ x <> load ==> lookup_var x sf = lookup_var x s) /\
      ptr_covers Gf tnf root sf N /\
      (!i. w2n addrw <= i /\ i < w2n addrw + 32 ==> i NOTIN tnf.t_mem))
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
        (strip_assume_tac o SRULE[gas_summary_ptr_at_marked]) >>
      qexists `marks` >> disj1_tac
      >- suspend "normal" >> suspend "exit") >>
  qexists `marks` >> disj2_tac >>
  drule force_exempt_cert >> metis_tac[]
QED

Resume structlit_first_memory_word_initialized_outcome[normal]:
  gvs[] >>
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o SRULE[gas_marked_exec_ptr_def]) >>
     drule gas_path_ptr_ok_not_halted >> simp[]) >>
  `emit_op ADD [buf.buf_operand; Lit 0w] sc = (Var dst,sm)` by simp[] >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    structlit_first_memory_word_initialized_consumer >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_expr _ _ (StructLit _ _ _) _ = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ALOOKUP _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (qspecl_then [`addrw`, `PG`, `cx_dead cx`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  irule (SRULE[] (Q.INST [`right` |-> `[]`] gas_summary_ptr_at_bind_normal)) >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  irule read_result_zero_ptr_summary >>
  goal_assum (drule_at (Pat `read_result _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  BETA_TAC >> qexistsl [`tv`, `s`, `G`, `tn`, `v`] >> simp[]
QED

Resume structlit_first_memory_word_initialized_outcome[exit]:
  Cases_on `res` >- fs[expr_exit_def] >>
  irule gas_summary_ptr_at_bind_exception >>
  goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
  Cases_on `y` >> Cases_on `r` >> fs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >> fs[expr_exit_def]
QED

Finalise structlit_first_memory_word_initialized_outcome
