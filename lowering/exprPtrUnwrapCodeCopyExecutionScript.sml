(* The allocation and copy counted paths retain the same raw copy endpoint. *)
Theory exprPtrUnwrapCodeCopyExecution
Ancestors
  exprPtrUnwrapCodeCopyShape exprPtrUnwrapAllocEntry exprPtrUnwrapAllocationFrame
  exprPtrUnwrapAllocSeparation exprPtrCodeCopyInduction exprPtrCodeCopyFrame
  exprLoweringProps loweringPosts compileEnv context bodyPtrDefs ptrDiscipline
  venomState venomInst words arithmetic finite_map fragGasPathPtr exprSimCopy
  exprSimAlloc bufferAllocationExecution

Theorem unwrap_runtime_code_execution:
  compile_alloc_buffer nb sm = (buf,mid) /\
  compile_imm_copy_to_memory F imm src buf.buf_operand n 0 mid = ((),sb) /\
  fn_has_code sm mid func /\ fn_has_code mid sb func /\
  stmt_state_rel ctx func cenv cx es s /\ nb < dimword (:256) /\ 32*n <= nb /\
  sm.cs_next_var <= mid.cs_next_var /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sm x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root u a Gm tm H tf z d.
    buf.buf_operand = Var root /\
    step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    Gm = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tm = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
    w2n d+nb < dimword (:256) /\
    copy_runtime_frame mid a sb z /\
    gas_path_ptr D 0 ctx func PG G tn s 0 H tf
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    z.vs_current_bb = sb.cs_current_bb /\ ~z.vs_halted /\
    ptr_covers H tf root z nb /\ lookup_var root a = SOME d /\
    tf.t_mem = tm.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} /\
    tf.t_stor = tm.t_stor /\ tf.t_trans = tm.t_trans /\ tf.t_imm = tm.t_imm /\
    (!x. not_fresh_at mid x ==> FLOOKUP H x = FLOOKUP Gm x /\
      op_taint tf (Var x) = op_taint tm (Var x)) /\
    (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory)
Proof
  strip_tac >> drule_all unwrap_alloc_entry >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `buf.buf_operand = Var root` >>
  `!x. src = Var x ==> x <> root` by
    metis_tac[unwrap_alloc_old_operand_distinct] >>
  drule_all unwrap_alloc_old_operand_ghost >>
  disch_then (qspecl_then [`tn`, `SUC s.vs_inst_idx`, `PG`, `G`] mp_tac) >>
  simp[] >> strip_tac >>
  qabbrev_tac `d:bytes32 = n2w (buffer_allocation_base s sm.cs_next_id)` >>
  `w2n d+nb < dimword (:256)` by
    (drule_all unwrap_alloc_site_bound >> simp[Abbr `d`]) >>
  drule_all allocated_copy_operands_old >> strip_tac >>
  `eval_operand src a = SOME p /\ op_taint tnf src = {}` by
    simp[eval_operand_def] >>
  `lookup_var root a = SOME d` by
    (qpat_x_assum `eval_operand buf.buf_operand a = _` mp_tac >>
     simp[eval_operand_def]) >>
  `allocas_from 0 a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    simp[allocas_from_def] >>
  qpat_assum `buf.buf_operand = Var root` (fn th =>
    qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  `0+32*n <= nb` by simp[] >>
  drule_all code_copy_range_ptr >>
  disch_then (qspecl_then [`func`, `PG`, `D`] strip_assume_tac) >>
  `~a.vs_halted` by
    (simp[buffer_allocation_fields_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas sm.cs_next_id` >> simp[]) >>
  drule_all code_copy_range_code_cursor >> strip_tac >>
  `copy_old_operand mid (Var root) /\ eval_operand (Var root) a = SOME d` by
    (pure_rewrite_tac[copy_old_operand_def, eval_operand_def] >>
     conj_tac >- (rpt strip_tac >> gvs[]) >> first_assum ACCEPT_TAC) >>
  `w2n d+32*n < dimword (:256)` by decide_tac >>
  `!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len a.vs_memory` by
    (rpt strip_tac >> irule code_copy_endpoint_exterior >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`)) >>
     qexistsl [`p`, `d`] >> asm_rewrite_tac[]) >>
  `ptr_covers Gf' tnf' root t nb` by metis_tac[] >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf' tnf'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    metis_tac[gas_path_ptr_then, ADD_0] >>
  qexistsl [`u`, `Gf'`, `tnf'`, `t`] >>
  gvs[Abbr `d`] >> first_assum ACCEPT_TAC
QED
