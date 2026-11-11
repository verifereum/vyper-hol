(* Allocation and immutable copy share one endpoint; only old roots are framed. *)
Theory exprPtrCodeCopyEndpoint
Ancestors
  exprPtrCodeCopyFrame exprPtrUnwrapEndpointFrames exprPtrUnwrapPostFrames
  exprPtrCodeCopyInduction exprSimCopy exprPtrUnwrapAllocationFrame
  freshWrites allocationPtr exprSimAlloc ptrDiscipline venomState venomInst
  finite_map arithmetic words pred_set exprPtrUnwrapAllocation compileEnv loweringStateRelDefs
  decoderGhostFramePtr bodyPtrDefs loweringPosts exprPtrUnwrapRetained
  exprSimStorageCopy exprLoweringProps

Theorem unwrap_code_old_variable_frames:
  compile_alloc_buffer nb sm = (buf,mid) /\ buf.buf_operand = Var root /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\
  G0 = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  copy_runtime_frame mid a sb z /\
  (!x. not_fresh_at mid x ==>
    FLOOKUP H x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) ==>
  !x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)
Proof
  strip_tac >> gen_tac >> disch_tac >>
  `not_fresh_at sm x /\ not_fresh_at mid x` by metis_tac[not_fresh_at_mono] >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `x <> root` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  `eval_operand (Var x) a = eval_operand (Var x) s` by
    (simp[] >> irule alloca_step_operand_preserved >>
     goal_assum (drule_at (Pat `step_inst_base _ _ = _`)) >> simp[]) >>
  `lookup_var x z = lookup_var x a` by metis_tac[copy_runtime_frame_def] >>
  `FLOOKUP H x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)` by
    (first_x_assum irule >> simp[]) >>
  fs[eval_operand_def] >>
  simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

Theorem unwrap_code_exterior_frames:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ nb < dimword (:256) /\
  buf.buf_operand = Var root /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  tn0 = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword (:256) /\
  32*n <= nb /\ a.vs_memory = s.vs_memory /\
  (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  tf.t_mem = tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} ==>
  (!j. j < w2n d \/ w2n d+nb <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)) /\
  (!off len. off+len <= w2n d \/ w2n d+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `root = STRING #"%" (toString sm.cs_next_var)` by fs[] >>
  qpat_x_assum `root = STRING _ _` SUBST_ALL_TAC >>
  `!j. j < w2n d \/ w2n d+nb <= j ==>
    (j IN tn0.t_mem <=> j IN tn.t_mem)` by
    (drule_all unwrap_alloc_taint_frame >>
     disch_then (qspec_then `tn` strip_assume_tac) >>
     gvs[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `~(w2n d <= j /\ j < w2n d+32*n)` by decide_tac >>
      `j IN tn0.t_mem <=> j IN tn.t_mem` by metis_tac[] >>
      qpat_x_assum `tf.t_mem = _` (fn th => rewrite_tac[th]) >>
      simp[]) >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >> decide_tac
QED

Theorem unwrap_code_ghost_inv:
  compile_alloc_buffer nb sm = (buf,mid) /\ fn_has_code sm mid func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  ghost_inv ret cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sm /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  buf.buf_operand = Var root /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = u with vs_inst_idx := k /\
  G0 = step_prov PG G (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
  tn0 = step_taint (mk_inst sm.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
  (d:bytes32) = n2w (buffer_allocation_base s sm.cs_next_id) /\
  buffer_allocation_base s sm.cs_next_id < dimword (:256) /\
  nb < dimword (:256) /\ 32*n <= nb /\ a.vs_memory = s.vs_memory /\
  a.vs_accounts = s.vs_accounts /\ a.vs_transient = s.vs_transient /\
  a.vs_call_ctx = s.vs_call_ctx /\ copy_runtime_frame mid a sb z /\
  tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
  (!x. not_fresh_at mid x ==>
    FLOOKUP H x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
  (!off len. off+len <= w2n d \/ w2n d+32*n <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len a.vs_memory) /\
  tf.t_mem = tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32*n} ==>
  ghost_inv ret cenv cx es H tf z
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==>
    lookup_var x z = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
    op_taint tf (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> irule unwrap_code_old_variable_frames >>
     goal_assum (drule_at (Pat `copy_runtime_frame _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >> simp[] >>
     qexistsl [`PG`, `k`, `sa`] >> asm_rewrite_tac[]) >>
  drule_all unwrap_code_exterior_frames >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `!name off len. local_region cenv es.scopes s name off len ==>
    w2n d+nb <= off \/ off+len <= w2n d` by
    (rpt strip_tac >> drule_all unwrap_alloc_local_separation >> simp[]) >>
  `stor_taint_ok cx tf z` by
    (irule copy_stor_taint_frame >> qexistsl [`s`, `tn`] >>
     fs[ghost_inv_def, copy_runtime_frame_def] >>
     qpat_x_assum `copy_static z = copy_static a`
       (mp_tac o Q.AP_TERM `\st. (st.vs_accounts,st.vs_transient,st.vs_call_ctx)`) >>
     simp[copy_static_def] >> gvs[]) >>
  irule unwrap_endpoint_ghost_inv >> (conj_tac >- simp[]) >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
  qexistsl [`nb`, `sa`, `w2n d`] >> asm_rewrite_tac[] >> metis_tac[]
QED
