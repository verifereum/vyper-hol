(* Fixed-size SHA input preparation and compiler shape boundaries. *)
Theory bodyPtrHashBuiltinsShaFixed
Ancestors bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsShaBytes
  builtinHashing emitHelper emitHelperProps compileEnv exprLoweringProps
  list rich_list arithmetic context fragGasSeqPtr ptrDiscipline venomState
  venomExecSemantics venomInst fragExec instIdxIndep words fragExecPtr ghostPcTransportPtr

Theorem hash_sha256_fixed_parts:
  compile_sha256_bytesm value m sa = (op,sb) ==>
  ?ib sl sm ob sn gas_op sg success_op sc sh.
    compile_alloc_buffer 32 sa = (ib,sl) /\
    emit_void MSTORE [ib.buf_operand;value] sl = ((),sm) /\
    compile_alloc_buffer 32 sm = (ob,sn) /\
    emit_op GAS [] sn = (gas_op,sg) /\
    emit_op STATICCALL [gas_op;Lit 2w;ib.buf_operand;Lit (n2w m);ob.buf_operand;Lit 32w] sg = (success_op,sc) /\
    emit_void ASSERT [success_op] sc = ((),sh) /\
    emit_op MLOAD [ob.buf_operand] sh = (op,sb)
Proof
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_sha256_bytesm_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  ntac 6 (pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) []) >>
  strip_tac >> gvs[] >>
  rpt (qpat_x_assum `emit_void _ _ _ = (u,_)` mp_tac >> Cases_on `u` >> strip_tac) >>
  metis_tac[]
QED

Theorem hash_sha256_word_bytesm:
  compile_sha256_word value = compile_sha256_bytesm value 32
Proof
  simp[compile_sha256_word_def, compile_sha256_bytesm_def]
QED

Theorem hash_fixed_prepare_emission:
  compile_alloc_buffer 32 sa = (ib,sl) /\
  emit_void MSTORE [ib.buf_operand;value] sl = ((),sm) ==>
  ib.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
  emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
       [Var (STRING #"%" (toString sa.cs_next_var));value] []] /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_next_var = sa.cs_next_var+1 /\ sm.cs_next_id = sa.cs_next_id+2
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]
QED

Theorem hash_alloc_store_counted:
  step_inst_base (mk_inst aid ALLOCA [Lit 32w] [p]) s = OK t /\
  lookup_var p t = SOME a /\ eval_operand value t = SOME w /\
  G1 = step_prov PG G (mk_inst aid ALLOCA [Lit 32w] [p]) t /\
  tn1 = step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn /\
  G2 = step_prov PG G1 (mk_inst sid MSTORE [Var p;value] []) (mstore (w2n a) w t) /\
  tn2 = step_taint (mk_inst sid MSTORE [Var p;value] []) t (mstore (w2n a) w t) tn1 /\
  ptr_covers G1 tn1 p t 32 /\ op_taint tn1 value = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst aid ALLOCA [Lit 32w] [p];
    mk_inst sid MSTORE [Var p;value] []] (DROP s.vs_inst_idx bb.bb_instructions) ==>
  run_inst_seq [mk_inst aid ALLOCA [Lit 32w] [p];
    mk_inst sid MSTORE [Var p;value] []] s = OK (mstore (w2n a) w t) /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
    (OK ((mstore (w2n a) w t) with vs_inst_idx := s.vs_inst_idx+2))
Proof
  strip_tac >>
  `step_inst_base (mk_inst sid MSTORE [Var p;value] []) t =
     OK (mstore (w2n a) w t)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  `run_inst_seq [mk_inst aid ALLOCA [Lit 32w] [p];
     mk_inst sid MSTORE [Var p;value] []] s = OK (mstore (w2n a) w t)` by
    simp[run_inst_seq_def] >> simp[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst aid ALLOCA [Lit 32w] [p]) s` by
    (irule ptr_inst_ok_alloca >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 (mk_inst sid MSTORE [Var p;value] [])
      (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ptr_inst_ok_mstore >> simp[ptr_covers_inst_idx]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst aid ALLOCA [Lit 32w] [p]; mk_inst sid MSTORE [Var p;value] []] s G2 tn2` by
    (gvs[inst_seq_ptr_def] >>
     simp[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
       exec_result_map_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst aid ALLOCA [Lit 32w] [p]; mk_inst sid MSTORE [Var p;value] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED
