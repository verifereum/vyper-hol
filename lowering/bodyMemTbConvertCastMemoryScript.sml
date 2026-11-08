(* A narrowing bytestring cast reads only the source length word. *)
Theory bodyMemTbConvertCastMemory
Ancestors
  bodyMemTbConvertLoadMemory exprLowering emitHelper compileEnv
  fragExecMem instMemFrontier venomExecSemantics venomState venomInst
  emitHelperProps exprLoweringProps list rich_list memSafeRun fragGasSeqMem
  bodyUnopFragMemory fragGasMode fragGasPathMem fragExec

Theorem convert_bytestring_cast_mem_ok:
  compile_type_convert v (ConvBytestringCast n k) sa = (op,sb) /\
  eval_operand v s = SOME w /\
  w2n w + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  Cases_on `n < k` >>
  gvs[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def]
  >- (`!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0`
        by decide_tac >>
      simp[DROP_APPEND, Once run_inst_seq_mem_ok_cons, mk_inst_def,
           below_frontier_MLOAD, inst_dload_in_section_def,
           step_inst_base_def, exec_read1_def, eval_operands_def] >>
      rewrite_tac[GSYM mk_inst_def] >>
      (conj_tac >- simp[below_frontier_MLOAD]) >>
      irule run_inst_seq_mem_ok_every >>
      simp[inst_dload_in_section_def] >> rpt conj_tac >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  simp[run_inst_seq_mem_ok_def]
QED

Theorem convert_bytestring_cast_slice[local]:
  compile_type_convert v (ConvBytestringCast n k) sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
             ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb) =
    LENGTH sb.cs_current_insts
Proof
  Cases_on `n < k` >>
  simp[compile_type_convert_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  `!j. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + j) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def,
       IS_PREFIX_APPEND, APPEND_ASSOC]
QED

Theorem convert_bytestring_cast_paths_mem:
  compile_type_convert v (ConvBytestringCast n k) sa = (op,sb) /\
  eval_operand v s = SOME w /\ w2n w + 32 <= s.vs_alloca_next /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))) /\
  (!a t. run_inst_seq (emitted_insts sa sb) s = Abort a t ==>
    ?j. gas_marked_path T ctx func s 0 (Abort a (t with vs_inst_idx := j)))
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule convert_bytestring_cast_mem_ok >> metis_tac[]) >>
  drule convert_bytestring_cast_slice >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, emitted_insts_def] >>
     simp[DROP_APPEND]) >>
  conj_tac >> rpt strip_tac
  >- (drule run_inst_seq_gas_path_mem >>
      disch_then (qspecl_then [`emitted_insts sa sb`, `t`, `ctx`, `func`, `bb`] mp_tac) >>
      simp[IS_PREFIX_APPEND] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  irule run_inst_seq_abort_zero_path_mem >>
  goal_assum (drule_at Any) >> simp[IS_PREFIX_APPEND] >>
  qexists_tac `emitted_insts sa sb` >> metis_tac[]
QED
