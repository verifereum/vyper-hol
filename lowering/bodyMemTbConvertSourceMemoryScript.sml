(* Full-capacity boundary for plain convert operands. *)
Theory bodyMemTbConvertSourceMemory
Ancestors
  exprSimMemDefs exprSimMemoryPath exprLowering compileEnv
  vyperValue valueEncoding venomState context
  fragGasSeqMem fragGasPathMem emitHelperProps instMemFrontier
  exprLoweringProps fragExecMem venomExecProofs rich_list
  emitHelper fragExec venomInst list vyperTypeSystem

Theorem convert_memory_unwrap_capacity:
  p.ptr_location = LocMemory /\ ~is_word_type t /\
  unwrap_value cenv (LocatedValue t p) sm = (op,sb) /\
  vv_store_bound cx t lt ee tv (LocatedValue t p) s /\
  evaluate_type (get_tenv cx) lt = SOME tvt /\
  eval_operand op s = SOME w ==>
  sb = sm /\ op = p.ptr_operand /\
  (type_memory_size tvt = 0 \/
   w2n w + type_memory_size tvt <= s.vs_alloca_next)
Proof
  strip_tac >>
  drule unwrap_memory_compile >> simp[] >> strip_tac >>
  gvs[comp_return_def, vv_store_bound_def] >>
  metis_tac[]
QED

Theorem convert_emit_mload_path_mem:
  emit_op MLOAD [arg] sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ alloca_inv s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var))
       (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions =
       [mk_inst sa.cs_next_id MLOAD [arg]
         [STRING #"%" (toString sa.cs_next_var)]] ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  drule run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then
    [`[mk_inst sa.cs_next_id MLOAD [arg]
        [STRING #"%" (toString sa.cs_next_var)]]`,
    `update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s`,
    `ctx`, `func`, `bb`] mp_tac) >>
  simp[is_terminator_def, run_inst_seq_mem_ok_def,
       run_inst_seq_def, below_frontier_MLOAD, step_MLOAD,
       mk_inst_def, IS_PREFIX_APPEND, venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, eval_operand_def,
       venomStateTheory.eval_operands_def, arithmeticTheory.ADD1]
QED

Theorem convert_stack_unwrap_capacity:
  ~is_word_type t /\
  unwrap_value cenv (StackValue t op0) sm = (op,sb) /\
  vv_store_bound cx t lt ee tv (StackValue t op0) s /\
  evaluate_type (get_tenv cx) lt = SOME tvt /\
  eval_operand op s = SOME w ==>
  sb = sm /\ op = op0 /\
  (type_memory_size tvt = 0 \/
   w2n w + type_memory_size tvt <= s.vs_alloca_next)
Proof
  strip_tac >>
  gvs[unwrap_value_def, comp_return_def, vv_store_bound_def] >>
  metis_tac[]
QED

(* The checker alone does not ensure a two-word source window. *)
Theorem convert_zero_bytes_capacity_probe:
  valid_conversion (BaseT (BytesT (Dynamic 0))) (BaseT BoolT) /\
  type_memory_bytes cenv (BaseT (BytesT (Dynamic 0))) = 32
Proof
  EVAL_TAC
QED
