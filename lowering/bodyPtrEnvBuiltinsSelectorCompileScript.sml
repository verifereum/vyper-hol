(* Compiler-facing runtime selector allocation/store suffix. *)
Theory bodyPtrEnvBuiltinsSelectorCompile
Ancestors bodyPtrEnvBuiltinsSelectorCounted bodyPtrEnvBuiltinsSelectorSuffix
  fragGasSeqPtr context emitHelper freshWrites
  exprLoweringProps compileEnv loweringStateRelDefs fragExec venomInst venomState
  bodyPtrDefs words list rich_list finite_map

Theorem selector_compile_code:
  compile_alloc_buffer 64 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 4w] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand; Lit 32w] sn = (data,sp) /\
  emit_void MSTORE [data; value] sp = ((),sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) ==>
  ?p q. buf.buf_operand = Var p /\ data = Var q /\
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p];
       mk_inst (sa.cs_next_id+1) MSTORE [Var p; Lit 4w] [];
       mk_inst (sa.cs_next_id+2) ADD [Var p; Lit 32w] [q];
       mk_inst (sa.cs_next_id+3) MSTORE [Var q; value] []] /\
    ~not_fresh_at sa p /\ ~not_fresh_at sa q /\ p <> q /\
    (!x. value = Var x ==> x <> p /\ x <> q) /\
    sb.cs_current_bb = sa.cs_current_bb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + 4
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, not_fresh_at_def] >>
  gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL, arithmeticTheory.LESS_EQ_ADD]
QED

Theorem selector_compile_counted:
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
  ~s.vs_halted /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sa G tn s G' tn' /\
    ptr_val_ok cx (BaseT (BytesT (Dynamic 4))) (BytesV bs) buf.buf_operand G' tn' t /\
    ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId args) buf.buf_operand G' t
Proof
  strip_tac >> drule_all selector_compile_code >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND, APPEND] >>
     qexists_tac `l` >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p]) (fn_insts fn)` by
    (irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
     qpat_x_assum `isPREFIX _ _` mp_tac >> simp[IS_PREFIX_APPEND] >> strip_tac >>
     `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w] [p])
       (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >> metis_tac[MEM_DROP_IMP]) >>
  qpat_x_assum `buf.buf_operand = _` SUBST1_TAC >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by simp[] >>
  pop_assum SUBST1_TAC >>
  drule_at (Pat `_ = [_;_;_;_]`) selector_suffix_certificate >>
  disch_then drule_all >>
  disch_then (qspecl_then [`args`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def]
QED
