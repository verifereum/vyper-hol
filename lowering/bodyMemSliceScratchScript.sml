(* Counted fixed-byte scratch allocation and store. *)
Theory bodyMemSliceScratch
Ancestors
  exprSimSliceFixedAdapter builtinBytesMemory allocationPtr abiBuiltinAllocation
  bodyMemAggregateBounds exprSimMemUnwrap fragGasSeqMem exprLoweringProps
  emitHelper emitHelperProps compileEnv context venomInst venomState
  allocaFootprint venomMemDefs list finite_map words bodyMemBiSha256Suffix
  fragExecMem instMemFrontier

Theorem slice_fixed_scratch_mem_ok[local]:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s /\
  fn_has_code sa sb func /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  run_inst_seq_mem_ok (emitted_insts sa sm ++ emitted_insts sm sb) s
Proof
  strip_tac >> drule_all slice_fixed_scratch_embedding >> strip_tac >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `!base cap. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (base,cap) ==> cap = 32` by
    (rpt strip_tac >> drule_all stmt_state_rel_alloca_site_bound >> simp[]) >>
  drule_all sha256_alloc32_mem >> strip_tac >>
  irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[] >>
  drule emitted_insts_emit_void >> strip_tac >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >> metis_tac[]
QED

Theorem slice_fixed_scratch_path_mem[local]:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sb) /\
  stmt_state_rel ctx func cenv cx es s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >> drule_all slice_fixed_scratch_code >> strip_tac >>
  `same_blocks sa sb` by
    (fs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[] >>
     gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_var_def, fresh_id_def, emit_def,
         same_blocks_def]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (CONV_TAC (LHS_CONV (REWR_CONV emitted_insts_def)) >>
     qpat_assum `sb.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
  drule_all slice_fixed_scratch_mem_ok >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  irule straight_path_mem >> simp[] >> qexists_tac `sa` >>
  simp[APPEND_ASSOC] >> fs[EVERY_MEM] >> gvs[]
QED

Theorem slice_fixed_scratch_entry_mem[local]:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; val_op] sm = ((),sb) /\
  eval_operand val_op s = SOME w /\
  (!x. val_op = Var x ==> not_fresh_at sa x) /\ (!l. val_op <> Label l) /\
  LENGTH bs <= 32 /\ TAKE (LENGTH bs) (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  alloca_history func s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u p. run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK u /\
    w2n p + LENGTH bs < dimword (:256) /\
    let u' = u with vs_inst_idx := LENGTH sb.cs_current_insts in
      gas_path_mem ctx func s 0 (OK u') /\ alloca_history func u' /\
      w2n p + 32 <= u'.vs_alloca_next /\ ~u'.vs_halted /\
      u'.vs_current_bb = sb.cs_current_bb /\
      stmt_state_rel ctx func cenv cx es u' /\
      eval_operand buf.buf_operand u' = SOME p /\
      mem_bytes_at (w2n p) (LENGTH bs) u'.vs_memory = bs /\
      (?x. buf.buf_operand = Var x /\ not_fresh_at sb x) /\
      (!sd se e1 e2 es1 es2 v1 v2 op1 op2 r1 r2.
        local_ptrs_reserved cenv sb /\ sb.cs_next_id <= sd.cs_next_id /\
        MAP FDOM es.scopes = MAP FDOM es1.scopes /\
        expr_post ctx func cenv cx e1 es sb sd u' es1 v1 op1 r1 /\
        expr_post ctx func cenv cx e2 es1 sd se r1 es2 v2 op2 r2 ==>
        mem_bytes_at (w2n p) (LENGTH bs) r2.vs_memory = bs)
Proof
  strip_tac >> drule_all slice_fixed_scratch_entry >> strip_tac >>
  drule_all slice_fixed_scratch_path_mem >> strip_tac >>
  drule_all slice_fixed_scratch_embedding >> strip_tac >>
  drule_all exprSimSliceMemoryTheory.slice_fixed_scratch_alloc >> strip_tac >>
  drule_all slice_fixed_scratch_code >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sm ++ emitted_insts sm sb) =
     LENGTH sb.cs_current_insts` by simp[] >>
  gvs[] >> rename1 `run_inst_seq _ s = OK result` >>
  `w2n p + 32 <= result.vs_alloca_next` by
    (irule aggregate_alloca_capacity_mem >> conj_tac
     >- (qexists_tac `sa.cs_next_id` >> simp[]) >>
     goal_assum (drule_at Any)) >>
  simp[] >> first_assum MATCH_ACCEPT_TAC
QED

Theorem slice_source_fixed_capture_entry_mem:
  expr_body_pre cenv cx env src es /\
  bind (eval_expr cx src) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  expr_post ctx func cenv cx src es sa sm s0 ee v src_op t /\
  expr_type src = BaseT (BytesT (Fixed m)) /\ m <= 32 /\
  lower_value compile_expr cenv (BaseT (BytesT (Fixed m))) src sa = (src_op,sm) /\
  compile_alloc_buffer 32 sm = (buf,sb) /\
  emit_void MSTORE [buf.buf_operand; src_op] sb = ((),sc) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  fn_inst_ids_distinct func /\ fn_has_code sm sc func /\ ~t.vs_halted /\
  alloca_history func t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bs u p. v = BytesV bs /\ LENGTH bs = m /\
    expr_sim_inv cenv cx env ee /\
    run_inst_seq (emitted_insts sm sb ++ emitted_insts sb sc) t = OK u /\
    w2n p + LENGTH bs < dimword (:256) /\
    let u' = u with vs_inst_idx := LENGTH sc.cs_current_insts in
      gas_path_mem ctx func t 0 (OK u') /\ alloca_history func u' /\
      w2n p + 32 <= u'.vs_alloca_next /\ ~u'.vs_halted /\
      u'.vs_current_bb = sc.cs_current_bb /\
      stmt_state_rel ctx func cenv cx ee u' /\
      eval_operand buf.buf_operand u' = SOME p /\
      mem_bytes_at (w2n p) (LENGTH bs) u'.vs_memory = bs /\
      (?x. buf.buf_operand = Var x /\ not_fresh_at sc x) /\
      (!sd se e1 e2 ee1 ee2 v1 v2 op1 op2 r1 r2.
        local_ptrs_reserved cenv sc /\ sc.cs_next_id <= sd.cs_next_id /\
        MAP FDOM ee.scopes = MAP FDOM ee1.scopes /\
        expr_post ctx func cenv cx e1 ee sc sd u' ee1 v1 op1 r1 /\
        expr_post ctx func cenv cx e2 ee1 sd se r1 ee2 v2 op2 r2 ==>
        mem_bytes_at (w2n p) (LENGTH bs) r2.vs_memory = bs)
Proof
  strip_tac >> drule_all slice_source_fixed_view >> strip_tac >>
  `!z. src_op = Var z ==> not_fresh_at sm z` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `!l. src_op <> Label l` by
    (drule_all exprSimSliceCaptureTheory.slice_source_operand_not_label >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee t` by
    fs[loweringPostsTheory.expr_post_def] >>
  `LENGTH bs <= 32` by decide_tac >>
  drule_all slice_fixed_scratch_entry_mem >> strip_tac >>
  qexistsl_tac [`bs`, `u`, `p`] >> simp[] >>
  first_assum MATCH_ACCEPT_TAC
QED
