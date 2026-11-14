(* Materialization preserves the child's physical post-value semantics. *)
Theory bodyPtrPhysicalChildUnwrap
Ancestors
  bodyPtrMakeArrayChildUnwrap bodyPtrMakeArrayExternalCaller
  bodyPtrMakeArrayNonwordUnwrap bodyPtrMakeArrayExternalUnwrap
  exprPtrUnwrapMarked exprSimHyps
  bodyPtrDefs loweringPosts exprLowering context compileEnv
  fragGasPathPtr fragGasPath exprSimHypsDefs valueCopyBytes typedMemoryCopy
  bodyPtrMakeArrayEmission bodyPtrMakeArrayAdd bodyPtrMakeArrayAddFrame
  bodyPtrMakeArrayAddCoverage emitHelperProps venomState venomExecSemantics
  ptrDiscipline wordArgsPtr vyperEvalExprPreservesScopesDom exprLoweringProps
  loweringStateRelDefs bodyPtrSubscriptSeamTupleLayoutBridge

Theorem unwrap_stack_physical_ptr_path:
  unwrap_value ce (StackValue t op) sm = (result,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (StackValue t op) s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (post_value_type ce e) raw (StackValue t op) ee G tn s /\
  ~s.vs_halted ==>
  sb = sm /\ result = op /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK s) /\
  expr_post ctx func ce cx e es sa sb s0 ee v result s /\
  ptr_val_ok cx (post_value_type ce e) v result G tn s
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def,
      vv_post_def, vv_holds_def, vv_at_def, vv_own_def] >>
  simp[cj 1 gas_path_ptr_rules, expr_post_def] >> metis_tac[]
QED

Theorem unwrap_memory_physical_ptr_path:
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  unwrap_value ce (LocatedValue t p) sm = (result,sb) /\
  vv_post ctx func ce cx e es sa sm s0 ee raw (LocatedValue t p) s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (post_value_type ce e) raw (LocatedValue t p) ee G tn s /\
  ~s.vs_halted ==>
  sb = sm /\ result = p.ptr_operand /\
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK s) /\
  expr_post ctx func ce cx e es sa sb s0 ee v result s /\
  ptr_val_ok cx (post_value_type ce e) v result G tn s
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def, ptr_vv_ok_def,
      vv_post_def, vv_holds_def, vv_at_def, vv_own_def] >>
  simp[cj 1 gas_path_ptr_rules, expr_post_def, ptr_val_ok_def,
       expr_val_rel_def, expr_val_at_def, expr_val_own_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
      metis_tac[]) >>
  strip_tac >> gvs[] >>
  imp_res_tac valueCopyBytesTheory.is_bytestring_word_type >> gvs[] >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> metis_tac[]
QED

Theorem literal_nonword_unwrap_physical:
  compile_expr ce (expr_type e) e si = (vv,sm) /\
  emit_op ADD [buf; Lit (n2w off)] sm = (Var out,sn) /\
  unwrap_value ce vv sn = (op,sb) /\ fn_has_code sn sb func /\
  eval_expr cx e esi = (INL raw,es') /\ read_result cx raw es' = (INL v,es') /\
  expr_body_pre ce cx env e esi /\ local_ptrs_reserved ce si /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
  vv_post ctx func ce cx e esi si sn s0 es' raw vv s /\
  ptr_vv_ok cx (post_value_type ce e) raw vv es' G tn s /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  (!t op. vv = StackValue t op ==> ptr_buf_ok ce e op G s) /\
  ghost_inv d ce cx es' G tn s /\ stmt_state_rel ctx func ce cx es' s /\
  s.vs_current_bb = sn.cs_current_bb /\ s.vs_inst_idx = LENGTH sn.cs_current_insts /\
  ~s.vs_halted /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~ce.ce_is_ctor /\ ~is_word_type (expr_type e) ==>
  ?z H tm.
    gas_path_ptr D 0 ctx func PG G tn s 0 H tm (OK z) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    expr_post ctx func ce cx e esi si sb s0 es' v op z /\
    ptr_val_ok cx (post_value_type ce e) v op H tm z /\ ptr_buf_ok ce e op H z /\
    (~is_bytestring_type (expr_type e) ==>
      ptr_mem_ok cx (lowered_value_type ce e) v op H tm z) /\
    ghost_inv d ce cx es' H tm z /\ ghost_kept ce es' sn G tn s H tm /\
    stmt_state_rel ctx func ce cx es' z /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\
    (!x n. not_fresh_at sn x /\ ptr_covers G tn x s n ==>
      ptr_covers H tm x z n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (post_value_type ce e)` by
    (`type_widens_to env.type_defs (post_value_type ce e) (expr_type e)` by
       (metis_tac[expr_body_pre_def, post_value_type_widens]) >>
     metis_tac[return_source_word_widens_eq]) >>
  `!z H tm. ptr_val_ok cx (post_value_type ce e) v op H tm z ==>
     (~is_bytestring_type (expr_type e) ==>
       ptr_mem_ok cx (lowered_value_type ce e) v op H tm z)` by
    metis_tac[aggregate_lowered_post_type, ptr_val_ok_def] >>
  Cases_on `vv`
  >- (drule_all unwrap_stack_physical_ptr_path >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
      qexistsl [`s`, `G`, `tn`] >> simp[ghost_kept_def]) >>
  rename1 `LocatedValue t p` >>
  `~is_word_type t` by
    (drule vv_post_located_type >> strip_tac >> gvs[] >>
     imp_res_tac valueCopyBytesTheory.is_bytestring_word_type >> gvs[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule_all unwrap_memory_physical_ptr_path >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
      qexistsl [`s`, `G`, `tn`] >> simp[ghost_kept_def]) >>
  `post_value_type ce e = expr_type e` by
    (drule_all external_located_post_type >> simp[]) >>
  gvs[] >> drule_all external_nonword_unwrap >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  gvs[] >> qexistsl [`z`, `H`, `tm`] >> simp[] >>
  (conj_tac >- metis_tac[gas_path_ptr_erase, gas_path_normal] >>
   rpt strip_tac >>
   drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`) unwrapped_old_pointer_coverage >>
   disch_then (qspecl_then [`z`, `x`, `n`] mp_tac) >> simp[])
QED
