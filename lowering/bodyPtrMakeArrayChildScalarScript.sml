(* Scalar counterpart of ChildUnwrap: retain the actual ADD and unwrap endpoint. *)
Theory bodyPtrMakeArrayChildScalar
Ancestors
  bodyPtrMakeArrayChildAdd bodyPtrMakeArrayScalarEndpoint
  emitHelperProps fragGasPathPtr fragGasPath loweringPosts compileEnv
  wordArgsPtr vyperEvalExprPreservesScopesDom exprLoweringProps

Theorem literal_child_scalar_materialize:
  !base cap.
  emit_op ADD [Var root; Lit (n2w off)] sm = (Var dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  fn_has_code sm sn func /\ fn_has_code sn su func /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ ~ce.ce_is_ctor /\ fn_inst_ids_distinct func /\
  lookup_var root s = SOME a /\ op_taint tn (Var root) = {} /\
  ptr_covers G tn root s capacity /\ FLOOKUP G root = SOME (base,cap) /\
  base+cap <= dimword(:256) /\ off < capacity /\ off+32 <= capacity /\
  vv_post ctx func ce cx e esi si sm s0 es' raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv es' G tn s /\ is_word_type (expr_type e) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  local_ptrs_reserved ce si /\ local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
  si.cs_next_var <= sm.cs_next_var /\ si.cs_next_var <= sn.cs_next_var /\
  si.cs_next_id <= sn.cs_next_id /\
  (!p. vv_operand vv = Var p ==> not_fresh_at sm p) /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at si p) /\
  ghost_inv d ce cx es' G tn s /\ ghost_kept ce esi si G0 tn0 s0 G tn ==>
  ?tv z H tm.
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    expr_post ctx func ce cx e esi si su s0 es' v op z /\
    eval_operand op z = SOME (typed_val_to_w256 tv v) /\ op_taint tm op = {} /\
    ghost_inv d ce cx es' H tm z /\ ghost_kept ce esi si G0 tn0 s0 H tm /\
    z.vs_current_bb = su.cs_current_bb /\ z.vs_inst_idx = LENGTH su.cs_current_insts /\
    ptr_covers H tm dst z 32 /\ lookup_var dst z = SOME (a+n2w off)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `(!t op. vv = StackValue t op /\ ~is_word_type (expr_type e) ==> ptr_buf_ok ce e op G s) /\
   (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
      ptr_buf_ok ce e p.ptr_operand G s)` by
    simp[] >>
  drule_all literal_child_add_endpoint >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `~z.vs_halted` by metis_tac[gas_path_ptr_erase, gas_path_normal] >>
  `(!p. vv_operand vv = Var p ==> not_fresh_at sn p) /\
   (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sn p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sn p)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `!name p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sn p` by
    gvs[local_ptrs_reserved_def] >>
  `not_fresh_at sn dst` by
    (drule emitted_insts_emit_op >> simp[not_fresh_at_def] >> metis_tac[]) >>
  drule_all scalar_unwrap_ptr_endpoint >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`ty`, `sf`, `Gf`, `tnf`] >> simp[] >>
  irule (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then |> SRULE []) >>
  qexistsl [`H`, `z`, `tm`] >> simp[]
QED
