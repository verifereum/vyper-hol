(* Counted storage forcing and post reconstruction share all execution witnesses. *)
Theory exprPtrUnwrapStorageRead
Ancestors
  exprPtrUnwrapStorageEndpoint exprPtrUnwrapEnsureExecution
  exprPtrUnwrapLoopEntry exprPtrUnwrapAllocSeparation exprPtrUnwrapAllocation
  exprLoweringProps loweringHalt gasSummaryComposePtr exprSimUnwrap
  bodyPtrDefs loweringPosts compileEnv context words arithmetic
  exprPtrUnwrapRuntimeFrame gasSummary exprSimUnwrapProps vyperState exprSimMemorySource

Theorem unwrap_storage_ensure_marked_read_ptr:
  compile_ensure_in_memory p.ptr_operand (slot_loc tr) nb n ctor imm sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  storage_holds cx tr (expr_type e) tv w ee s /\
  p.ptr_location = slot_loc tr /\ eval_operand p.ptr_operand s = SOME w /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s /\
  op_taint tn p.ptr_operand = {} /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id < sb.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\ n = type_slot_size ty /\
  type_memory_size ty <= nb /\ 32*n <= nb /\ nb < dimword (:256) /\ n < 2**256 /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= nb /\
  ghost_inv ret cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv ret cenv cx ee H tf z /\
    ptr_val_ok cx (expr_type e) v op H tf z /\ ptr_buf_ok cenv e op H z /\
    ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  `slot_loc tr = LocStorage \/ slot_loc tr = LocTransient` by
    (Cases_on `tr` >> simp[slot_loc_def]) >>
  `create_memory_snapshot [] s /\
   EVERY (\(off,bs). off+LENGTH bs <= LENGTH s.vs_memory /\
     (off+LENGTH bs <= buffer_allocation_base s sm.cs_next_id \/
       buffer_allocation_base s sm.cs_next_id+32*n <= off)) []` by
    simp[createSourceCallbackTheory.create_memory_snapshot_def] >>
  drule_at (Pat `compile_ensure_in_memory _ _ _ _ _ _ _ = _`)
    unwrap_ensure_slot_execution >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `create_memory_snapshot _ _`)) >>
  disch_then (drule_at (Pat `op_taint _ _ = {}`)) >>
  disch_then (qspecl_then [`PG`, `G`, `cx_dead cx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `slot_copy_runtime_frame mid d n a z` >>
  `sm.cs_next_var <= mid.cs_next_var` by
    (mp_tac (Q.SPECL [`nb`, `sm`] ci_mono_compile_alloc_buffer) >>
     asm_rewrite_tac[] >> simp[ci_mono_def]) >>
  drule_all unwrap_alloc_site_bound >> disch_tac >>
  `buffer_allocation_base s sm.cs_next_id < dimword (:256)` by decide_tac >>
  drule_all unwrap_alloc_loop_external >> strip_tac >>
  `eval_operand (Var root) z = SOME d` by
    (fs[slot_copy_runtime_frame_def] >> metis_tac[venomStateTheory.eval_operand_def]) >>
  `(!j. j < n ==> mem_word_at (w2n d+32*j) z.vs_memory =
      slot_copy_word (if tr then TLOAD else SLOAD) s (w+n2w j)) /\
   (!j b. j < n /\ b < 32 /\ w2n d+32*j+b IN tnf.t_mem ==>
      b IN key_taint (if tr then tn.t_trans else tn.t_stor) (w+n2w j))` by
    (Cases_on `tr` >> gvs[slot_loc_def]) >>
  `tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by asm_rewrite_tac[] >>
  `?v. read_result cx tv ee = (INL v,ee) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v (Var root) z /\
    ghost_inv ret cenv cx ee Gf tnf z /\
    ptr_val_ok cx (expr_type e) v (Var root) Gf tnf z /\
    ptr_buf_ok cenv e (Var root) Gf z /\ ghost_kept cenv es sa Gi ti s0 Gf tnf` by
    (irule unwrap_storage_endpoint_post >>
     ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
     goal_assum (drule_at (Pat `slot_copy_runtime_frame _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `_ = step_prov _ _ _ _`)) >>
     goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
     qexistsl [`buf`, `SUC s.vs_inst_idx`, `tn0`, `ty`] >> asm_rewrite_tac[]) >>
  pop_assum strip_assume_tac >>
  qexistsl [`v`, `Gf`, `tnf`, `z`] >>
  simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
  metis_tac[read_result_gas_obs]
QED
