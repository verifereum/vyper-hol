Theory bodyIntCallJointTuple
Ancestors
  bodyIntCallJointWrite exprLowering context compileEnv emitHelperProps
  fragGasSeq fragGasPath list rich_list vyperAST exprCallBounds
  exprLoweringProps fragExec venomInst venomInstProofs venomExecSemantics
  emitHelper venomState

(* Isolate the actual singleton compiler before its execution proof. *)
Theorem joint_singleton_tuple_compile:
  compile_alloc_buffer (type_memory_bytes ce (expr_type e)) sa = (buf,sm) /\
  compile_expr ce (expr_type e) e sm = (StackValue et src,sn) /\
  emit_op ADD [buf.buf_operand; Lit 0w] sn = (dst,sp) /\
  compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) sp =
    ((),sb) ==>
  compile_expr ce ty (Builtin ann (MakeArray NONE bnd) [e]) sa =
    (LocatedValue ann (mk_ptr buf.buf_operand LocMemory),sb)
Proof
  strip_tac >> Cases_on `e` >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_expr_body_def, builtin_child_callback_def,
       expr_builtin_dispatch_bound, expr_type_def] >>
  once_rewrite_tac[compile_expr_raw_def] >>
  simp[compile_builtin_dispatch_body_def, as_ptr_val_def] >>
  simp[compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, unwrap_value_def, as_ptr_val_def]
QED

(* The allocation prefix contributes no gas reads, at its actual endpoint. *)
Theorem joint_tuple_alloc_prefix_path:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  gas_path ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
  sm.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >>
  `?op. emit_op ALLOCA [Lit (n2w sz)] sa = (op,sm)` by
    (gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, IS_PREFIX_APPEND] >> simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sm)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all tuple_run_inst_seq_gas_path >> simp[mk_inst_def]
QED

(* Exit propagation does not impose a successful-value frame on the child. *)
Theorem joint_singleton_tuple_exit_path:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sz < dimword (:256) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (~?u. r = OK u) /\
  (!t. run_inst_seq (emitted_insts sa sm) s = OK t ==>
    gas_path ctx func (t with vs_inst_idx := LENGTH sm.cs_current_insts) n r) ==>
  gas_path ctx func s n r
Proof
  strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all exprSimAllocTheory.literal_alloc_buffer_run >> strip_tac >>
  drule_all joint_tuple_alloc_prefix_path >> strip_tac >>
  qpat_x_assum `!t. run_inst_seq _ _ = _ ==> _` drule >> strip_tac >>
  qpat_x_assum `!ctx. _` (qspec_then `ctx` strip_assume_tac) >>
  drule_all gas_path_then >> simp[]
QED
