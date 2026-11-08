(* Uniform dispatch reuses word and zero/flat endpoints; only bytes require
   the annotation-level uniform forcing boundary. *)
Theory bodyPtrStructLitUniformEndpoint
Ancestors bodyPtrStructLitUniformBytesEndpoint bodyPtrStructLitUniformTypes
  bodyPtrMakeArrayConsOutcome bodyPtrMakeArrayConsLayout exprSimHypsDefs

Theorem structlit_uniform_cons_endpoint:
  literal_loop_frame ctx func ce cx d root aid addr capacity
    ees fr sf Gf tnf esi si G0 tn0 s0 cells off /\
  literal_prefix_ok cells tn0 s0 /\ stmt_state_rel ctx func ce cx ees sf /\
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op (Var dst) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  fn_has_code si sb func /\ local_ptrs_reserved ce si /\ local_ptrs_reserved ce fr /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\ ~ce.ce_is_ctor /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ value_has_type tv v /\ k = type_memory_bytes ce (expr_type e) /\
  off+k <= capacity /\ post_value_type ce e = expr_type e /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~s.vs_halted /\ lookup_var root s = SOME (n2w addr) /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (addr,capacity) /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\
  (!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    literal_loop_frame ctx func ce cx d root aid addr capacity
      ees fr sf Gf tnf es' sb H tm z (cells ++ [(tv,v,addr+off,k)]) (off+k) /\
    literal_prefix_ok (cells ++ [(tv,v,addr+off,k)]) tm z
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type (expr_type e)`
  >- (drule_all literal_annotation_slot >> strip_tac >>
      `k = 32` by metis_tac[] >>
      `off+32 <= capacity` by metis_tac[] >>
      drule_all literal_cons_word_endpoint >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >> gvs[]) >>
  `!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s` by metis_tac[] >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- (drule_all structlit_uniform_cons_bytes_endpoint >> simp[]) >>
  `well_typed_expr env e` by gvs[expr_body_pre_def] >>
  `lowered_value_type ce e = expr_type e` by
    (drule_all structlit_uniform_nonword_lowered_type >> simp[]) >>
  Cases_on `k = 0`
  >- (`op_taint tn (Var root) = {}` by gvs[bodyPtrDefsTheory.ptr_covers_def] >>
      `type_memory_bytes ce (expr_type e) = 0` by metis_tac[] >>
      drule_all literal_cons_zero_endpoint >>
      disch_then (qspecl_then [`PG`, `D`] mp_tac) >> gvs[]) >>
  `0 < k` by decide_tac >> drule_all literal_cons_flat_endpoint >> simp[]
QED
