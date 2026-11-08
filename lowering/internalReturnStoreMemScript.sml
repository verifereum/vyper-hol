(* Store-memory checking at a typed internal-return boundary. *)
Theory internalReturnStoreMem
Ancestors
  bodyDeclMemoryCore bodyDeclCopyMemory exprSimMemDefs
  exprSimBufferStore bodyCopyMemory instMemFrontier
  exprSimProps loweringPosts context emitHelperProps emitHelper
  compileEnv venomState venomInst fragExec fragExecMem exprLoweringProps
  tupleTargetStoreRun fragGasSeqMem fragGasPathMem list rich_list valueCopy

Theorem internal_return_store_mem_ok[local]:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (gvs[compile_store_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >> gvs[]) >>
  `?w. eval_operand src s = SOME w /\
       val_in_memory tv v (w2n w) s.vs_memory` by gvs[expr_val_rel_def] >>
  Cases_on `type_memory_size tv = 0`
  >- (`val_store_size tv v = 0` by
        (drule val_store_size_le >> simp[]) >>
      `~is_bytestring_type ty` by
        (strip_tac >> drule_all buffer_typed_bytestring_header >> simp[]) >>
      gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
          emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  `0 < val_store_size tv v` by metis_tac[val_store_size_pos, arithmeticTheory.NOT_ZERO_LT_ZERO] >>
  `w2n w + val_store_size tv v <= s.vs_alloca_next` by
    (fs[expr_store_bound_def] >> gvs[]) >>
  irule body_typed_store_memory_mem_ok >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem internal_return_store_path_mem:
  compile_store_memory ce src dst ty ty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_bytes ce ty = type_memory_size tv /\
  w2n d + type_memory_size tv + 64 < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
      run_inst_seq (emitted_insts sa sb) s = OK t /\
      val_in_memory tv v (w2n d) t.vs_memory /\
      (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `?w. eval_operand src s = SOME w /\
       (if is_word_type ty then w = typed_val_to_w256 tv v
        else val_in_memory tv v (w2n w) s.vs_memory)` by
    gvs[expr_val_rel_def] >>
  `!x. src = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `!x. dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all compile_store_memory_run >> strip_tac >>
  `type_memory_size tv < dimword (:256)` by decide_tac >>
  drule_all internal_return_store_mem_ok >> strip_tac >>
  drule tuple_local_copy_code_shape >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (qpat_x_assum `sb.cs_current_insts = sa.cs_current_insts ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> gvs[]
QED
